import Calderon.ActualHighAdjointWeightedCorrectionPointwiseIdentity
import Calderon.ActualLowerAdjointMovingQuotientOrderedWords
import Calderon.ActualPairedAdjointRadiusPowerWeightedWordBounds
import Calderon.ActualReferenceSignedRemainderPivot
import Calderon.ActualMovingBoundaryTransposeIdentification
import Calderon.ActualHighMovingBoundaryFamily
import Calderon.ActualAdjointMovingBoundaryAction
import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.LocalCoordinateWordJetLinearOperations
import Calderon.LocalAffineCoordinateWordJetTransport
import Calderon.FinitePairedEndpointJetBounds
import Calderon.JointRadialDerivativeLocalSmoothness
import Calderon.ActualJacobiNativeMultiplierProfileLocalSmoothness
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus
import Calderon.ActualNativeMovingLocalRemainderCompatibility

/-! SAME actual ordered pivot correction. Full literal before-code6 inventory v007,
local open products v009, direct radial/coordinate/Jacobi pivots v010.
All6 ordinary names mandatory. This active author source is held and uncompiled. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame SmoothMetricFrame MovingFrameConnection
  NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
  ActualReferenceLocalCoordinateWordJets ActualReferenceDDHigherGeometryJets
  ActualReferenceDDHigherHCoframeJets ActualReferenceDDHigherLogFrameJets
  ConformalDepth RadiusProfile ActualHigherRadiusProfile ReferenceWeightedApproximation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local instance actualPhysicalPivotHalfComplete : CompleteSpace Half := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance actualPhysicalPivotNegComplete : CompleteSpace Neg := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance actualPhysicalPivotHighIsBoundedSMul : IsBoundedSMul ℝ (Hi →L[ℝ] Half) :=
  @NormedSpace.toIsBoundedSMul ℝ (Hi →L[ℝ] Half) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ) (E := Hi) (F := Half) (σ₁₂ := RingHom.id ℝ))

local instance actualPhysicalPivotLowIsBoundedSMul : IsBoundedSMul ℝ (Half →L[ℝ] Neg) :=
  @NormedSpace.toIsBoundedSMul ℝ (Half →L[ℝ] Neg) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup (E := Half) (F := Neg) (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ) (E := Half) (F := Neg) (σ₁₂ := RingHom.id ℝ))

local instance actualPhysicalPivotHalfEndIsBoundedSMul : IsBoundedSMul ℝ (Half →L[ℝ] Half) :=
  @NormedSpace.toIsBoundedSMul ℝ (Half →L[ℝ] Half) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ) (E := Half) (F := Half) (σ₁₂ := RingHom.id ℝ))

local instance actualPhysicalPivotNegEndIsBoundedSMul : IsBoundedSMul ℝ (Neg →L[ℝ] Neg) :=
  @NormedSpace.toIsBoundedSMul ℝ (Neg →L[ℝ] Neg) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup (E := Neg) (F := Neg) (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ) (E := Neg) (F := Neg) (σ₁₂ := RingHom.id ℝ))

def referenceAdjointMovingDifferenceQuotientPivotHigh
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  let r : ℝ := R y
  let S : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let D : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    deriv (fun t : ℝ => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
  let C0 : Fin 3 → SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun j =>
    referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
  let M : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun j =>
    sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
  let N : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun j =>
    nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,r)))
  let f : ℝ := referenceRadiusHorizontalLogDerivative g L q R y i
  (M i).comp S + (∑ j : Fin 3, (N j).comp (C0 j)) +
    r • (∑ j : Fin 3, (N j).comp ((M j).comp D)) +
    r^2 • (∑ j : Fin 3, (N j).comp ((M j).comp S)) + (r*f) • S

def referenceAdjointMovingDifferenceQuotientPivotLow
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (R : R3 → ℝ) (y : R3) (i : Fin 3) :
    SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
  let r : ℝ := R y
  let S : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r
  let D : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    deriv (fun t : ℝ => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
  let C0 : Fin 3 → SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun j =>
    referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
  let M : Fin 3 → SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun j =>
    sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
  let N : Fin 3 → SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) := fun j =>
    nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j (q,(y,r)))
  let f : ℝ := referenceRadiusHorizontalLogDerivative g L q R y i
  (M i).comp S + (∑ j : Fin 3, (N j).comp (C0 j)) +
    r • (∑ j : Fin 3, (N j).comp ((M j).comp D)) +
    r^2 • (∑ j : Fin 3, (N j).comp ((M j).comp S)) + (r*f) • S

attribute [local irreducible] harmonicSphereSubspace referenceAdjointMovingDifferenceQuotientPivotHigh
  referenceAdjointMovingDifferenceQuotientPivotLow referenceSharpRadialTraceFamily
  referenceLowerRadialEndpointFamily referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceSharpRadialTraceSecondRemainder
  referenceLowerRadialTraceSecondRemainder referenceRadialEndpointInvertibleLocus
  nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL nativeThreeHalfCoefficientMulL
  referenceHighCoordinateBoundaryFamily referenceLowerCoordinateBoundaryFamily
  referenceHighAdjointCoordinateBoundaryFamily referenceLowerAdjointCoordinateBoundaryFamily
  referenceHighAdjointMovingDifferenceQuotient referenceLowerAdjointMovingDifferenceQuotient
  referenceJacobiBoundaryCoefficientFamily referenceJacobiBoundaryThreeHalfCoefficientFamily
  sphereSobolevLinearCoordinateMulL sphereSobolevInclusionL secondTaylorRemainder

lemma deriv_intertwining_clm_of_eventuallyEq
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : ℝ → X) (G : ℝ → Y) (P : X →L[ℝ] Z) (Q : Y →L[ℝ] Z) (r : ℝ)
    (hF : DifferentiableAt ℝ F r) (hG : DifferentiableAt ℝ G r)
    (hNear : (fun t : ℝ => P (F t)) =ᶠ[𝓝 r] (fun t : ℝ => Q (G t))) :
    P (deriv F r) = Q (deriv G r) := by
  have hP : HasDerivAt (fun t : ℝ => P (F t)) (P (deriv F r)) r :=
    P.hasFDerivAt.comp_hasDerivAt r hF.hasDerivAt
  have hQ : HasDerivAt (fun t : ℝ => Q (G t)) (Q (deriv G r)) r :=
    Q.hasFDerivAt.comp_hasDerivAt r hG.hasDerivAt
  exact hP.unique (hQ.congr_of_eventuallyEq hNear)

lemma referenceSharpRadialTraceFamily_deriv_zero_lower_compatibility
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3)
    (h0 : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (deriv (fun t : ℝ => referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0) =
      (deriv (fun t : ℝ => referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0).comp
          (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let I : Hi →L[ℝ] Half := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : Half →L[ℝ] Neg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let p0 : ℝ × (R3 × ℝ) := (q,(y,0))
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let Dh : ℝ → Hi →L[ℝ] Half := fun t => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let Dl : ℝ → Half →L[ℝ] Neg := fun t => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  have h0P := h0
  change p0 ∈ Ω at h0P
  unfold Ω referenceRadialEndpointInvertibleLocus at h0P
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hSlice : Continuous (fun t : ℝ => (q,(y,t))) := continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, (q,(y,t)) ∈ Ω :=
    hSlice.continuousAt.preimage_mem_nhds (hΩ.mem_nhds h0)
  have hDh : DifferentiableAt ℝ Dh 0 :=
    ((contDiffAt_referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 h0P.1).comp 0
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have hDl : DifferentiableAt ℝ Dl 0 :=
    ((contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 h0P.2.2 h0P.2.1).comp 0
      (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have hCompatNear : (fun t : ℝ => J.comp (Dh t)) =ᶠ[𝓝 0] (fun t => (Dl t).comp I) := by
    filter_upwards [hNear] with t ht
    have hRaw := referenceSharpRadialTraceFamily_lower_compatibility_on_locus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t)) ht
    change J.comp (Dh t) = (Dl t).comp I at hRaw
    exact hRaw
  have hDerivativeCompatRaw := deriv_intertwining_clm_of_eventuallyEq
    Dh Dl (ContinuousLinearMap.compL ℝ Hi Half Neg J)
    ((ContinuousLinearMap.compL ℝ Hi Half Neg).flip I) 0 hDh hDl hCompatNear
  have hDerivativeCompat : J.comp (deriv Dh 0) = (deriv Dl 0).comp I := by
    simpa only [ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply] using hDerivativeCompatRaw
  change J.comp (deriv Dh 0) = (deriv Dl 0).comp I
  exact hDerivativeCompat

lemma referenceAdjointMovingDifferenceQuotientPivot_inclusion
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (hr : R y ≠ 0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (i : Fin 3) :
    (sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)).comp
      (referenceAdjointMovingDifferenceQuotientPivotHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) =
    (referenceAdjointMovingDifferenceQuotientPivotLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i).comp
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)) := by
  let I : Hi →L[ℝ] Half := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : Half →L[ℝ] Neg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let p0 : ℝ × (R3 × ℝ) := (q,(y,0))
  let pR : ℝ × (R3 × ℝ) := (q,(y,R y))
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let Dh : ℝ → Hi →L[ℝ] Half := fun t => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let Dl : ℝ → Half →L[ℝ] Neg := fun t => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  have h0 : p0 ∈ Ω := by simpa only [p0,zero_mul] using hSegment 0 ⟨le_rfl,zero_le_one⟩
  have h0P := h0
  unfold Ω referenceRadialEndpointInvertibleLocus at h0P
  have hDerivativeCompatRaw := referenceSharpRadialTraceFamily_deriv_zero_lower_compatibility
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y h0
  have hDerivativeCompat : J.comp (deriv Dh 0) = (deriv Dl 0).comp I := by
    change J.comp (deriv Dh 0) = (deriv Dl 0).comp I at hDerivativeCompatRaw
    exact hDerivativeCompatRaw
  have hS : J.comp (referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)) =
      (referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)).comp I :=
    referenceSharpRadialTraceSecondRemainder_lower_compatibility g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y) hSegment
  have hC (j : Fin 3) : J.comp (referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j) =
      (referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j).comp I :=
    referenceCoordinateBoundaryFamily_high_lower_compatibility g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j h0P.2.2 h0P.1 h0P.2.1
  let Mh : Fin 3 → Half →L[ℝ] Half := fun j => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
  let Ml : Fin 3 → Neg →L[ℝ] Neg := fun j => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
  let Nh : Fin 3 → Half →L[ℝ] Half := fun j => nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j pR)
  let Nl : Fin 3 → Neg →L[ℝ] Neg := fun j => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j pR)
  have hM (j : Fin 3) (v : Half) : J (Mh j v) = Ml j (J v) :=
    sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (EuclideanSpace.single j 1) v
  have hN (j : Fin 3) (v : Half) : J (Nh j v) = Nl j (J v) :=
    congrArg (fun A : Half →L[ℝ] Neg => A v)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j pR))
  have hSv (v : Hi) : J (referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y) v) =
      referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y) (I v) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A v) hS
  have hDv (v : Hi) : J (deriv Dh 0 v) = deriv Dl 0 (I v) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A v) hDerivativeCompat
  have hCv (j : Fin 3) (v : Hi) : J (referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j v) =
      referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j (I v) :=
    congrArg (fun A : Hi →L[ℝ] Neg => A v) (hC j)
  apply ContinuousLinearMap.ext
  intro u
  simp only [referenceAdjointMovingDifferenceQuotientPivotHigh,
    referenceAdjointMovingDifferenceQuotientPivotLow,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    map_add,map_sum,map_smul]
  change J (Mh i (referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y) u)) +
      (∑ j : Fin 3, J (Nh j (referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j u))) +
      R y • (∑ j : Fin 3, J (Nh j (Mh j (deriv Dh 0 u)))) +
      (R y)^2 • (∑ j : Fin 3, J (Nh j (Mh j (referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y) u)))) +
      (R y * referenceRadiusHorizontalLogDerivative g L q R y i) • J (referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y) u) = _
  simp only [hM,hN,hSv,hDv,hCv]
  rfl

lemma referenceAdjointHalfRadialFamily_deriv_zero_eq_transpose
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (q : ℝ) (y : R3)
    (h0 : (q,(y,0)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    deriv (fun t : ℝ => referenceAdjointHalfRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0 =
      sphereLowerDistributionalTranspose (deriv (fun t : ℝ => referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0) := by
  let p0 : ℝ × (R3 × ℝ) := (q,(y,0))
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let Ad : ℝ → Half →L[ℝ] Neg := fun t => referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let Dr : ℝ → Half →L[ℝ] Neg := fun t => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hSlice : ContDiff ℝ ∞ (fun t : ℝ => (q,(y,t))) := contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hNear : ∀ᶠ t : ℝ in 𝓝 0, (q,(y,t)) ∈ Ω :=
    hSlice.continuous.continuousAt.preimage_mem_nhds (hΩ.mem_nhds h0)
  have hAd : DifferentiableAt ℝ Ad 0 := by
    have hOuter : ContDiffAt ℝ ∞
        (fun z : ℝ × (R3 × ℝ) => referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z) p0 :=
      (contDiffOn_referenceAdjointHalfRadialFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt
        (hΩ.mem_nhds h0)
    have hComposed := ContDiffAt.fun_comp
      (f := fun t : ℝ => (q,(y,t)))
      (g := fun z : ℝ × (R3 × ℝ) => referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z)
      0 hOuter hSlice.contDiffAt
    exact hComposed.differentiableAt (by simp)
  have hDr : DifferentiableAt ℝ Dr 0 := by
    have hOuter : ContDiffAt ℝ ∞
        (fun z : ℝ × (R3 × ℝ) => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z) p0 :=
      (contDiffOn_referenceLowerRadialEndpointFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).contDiffAt
        (hΩ.mem_nhds h0)
    have hComposed := ContDiffAt.fun_comp
      (f := fun t : ℝ => (q,(y,t)))
      (g := fun z : ℝ × (R3 × ℝ) => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z)
      0 hOuter hSlice.contDiffAt
    exact hComposed.differentiableAt (by simp)
  have hAdNear : Ad =ᶠ[𝓝 0] (fun t : ℝ => sphereLowerDistributionalTranspose (Dr t)) := by
    filter_upwards [hNear] with t ht
    have htFields := ht
    unfold Ω referenceRadialEndpointInvertibleLocus at htFields
    have hRaw := sphereLowerDistributionalTranspose_referenceLowerRadial
      g L y0 Φ B ε C ρ H a w hData τ0 hcalc hF hO hD (q,(y,t)) htFields.2.1
    change sphereLowerDistributionalTranspose (Dr t) = Ad t at hRaw
    exact hRaw.symm
  have hAdNearL : Ad =ᶠ[𝓝 0] (fun t : ℝ => sphereLowerDistributionalTransposeL (Dr t)) := by
    filter_upwards [hAdNear] with t ht
    exact ht.trans (sphereLowerDistributionalTransposeL_apply (Dr t)).symm
  let Pid : (Half →L[ℝ] Neg) →L[ℝ] (Half →L[ℝ] Neg) :=
    ContinuousLinearMap.id ℝ (Half →L[ℝ] Neg)
  let Qtranspose : (Half →L[ℝ] Neg) →L[ℝ] (Half →L[ℝ] Neg) :=
    sphereLowerDistributionalTransposeL
  have hAdNearTyped : (fun t : ℝ => Pid (Ad t)) =ᶠ[𝓝 0]
      (fun t : ℝ => Qtranspose (Dr t)) := by
    simpa only [Pid,Qtranspose,ContinuousLinearMap.id_apply] using hAdNearL
  have hDerivativeTransposeRaw := deriv_intertwining_clm_of_eventuallyEq
    (X := Half →L[ℝ] Neg) (Y := Half →L[ℝ] Neg) (Z := Half →L[ℝ] Neg)
    Ad Dr Pid Qtranspose 0 hAd hDr hAdNearTyped
  have hDerivativeTranspose : deriv Ad 0 = sphereLowerDistributionalTranspose (deriv Dr 0) := by
    simpa only [Pid,Qtranspose,ContinuousLinearMap.id_apply,
      sphereLowerDistributionalTransposeL_apply] using hDerivativeTransposeRaw
  change deriv Ad 0 = sphereLowerDistributionalTranspose (deriv Dr 0)
  exact hDerivativeTranspose

lemma sphereSobolevDualPairing_referenceAdjointMovingDifferenceQuotientPivot
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (y : R3) (hy : ‖y-y0‖ ≤ ρ) (hr : R y ≠ 0)
    (hInv : ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (i : Fin 3) (u : SphereSobolev (3/2 : ℝ)) (z : SphereSobolev (1/2 : ℝ)) :
    (sphereSobolevDualPairing (1/2 : ℝ)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)
      (referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i z) =
      ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) z,
        sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
          (referenceAdjointMovingDifferenceQuotientPivotHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i u)⟫_ℝ) ∧
    (sphereSobolevDualPairing (1/2 : ℝ)
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) u)
      (referenceAdjointMovingDifferenceQuotientPivotLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i z) =
      ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) z,
        sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
          (referenceHighAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i u)⟫_ℝ) := by
  classical
  let I : Hi →L[ℝ] Half := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : Half →L[ℝ] Neg := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z : Half →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let Q : Half → Neg → ℝ := sphereSobolevDualPairing (1/2 : ℝ)
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let p0 : ℝ × (R3 × ℝ) := (q,(y,0))
  let pR : ℝ × (R3 × ℝ) := (q,(y,R y))
  let Ad : ℝ → Half →L[ℝ] Neg := fun t => referenceAdjointHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let Dr : ℝ → Half →L[ℝ] Neg := fun t => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))
  let Tl : Half →L[ℝ] Neg := secondTaylorRemainder Ad (R y)
  let Sl : Half →L[ℝ] Neg := referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)
  let Sh : Hi →L[ℝ] Half := referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y)
  let C0a : Fin 3 → Half →L[ℝ] Neg := fun j => referenceLowerAdjointCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j
  let C0d : Fin 3 → Half →L[ℝ] Neg := fun j => referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j
  let Mh : Fin 3 → Half →L[ℝ] Half := fun j => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
  let Ml : Fin 3 → Neg →L[ℝ] Neg := fun j => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
  let Nh : Fin 3 → Half →L[ℝ] Half := fun j => nativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j pR)
  let Nl : Fin 3 → Neg →L[ℝ] Neg := fun j => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
    (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j pR)
  let El : Half →L[ℝ] Neg := referenceLowerAdjointMovingDifferenceQuotient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  let Ebl : Half →L[ℝ] Neg := referenceAdjointMovingDifferenceQuotientPivotLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i
  have h0 : p0 ∈ Ω := by simpa only [p0,zero_mul] using hSegment 0 ⟨le_rfl,zero_le_one⟩
  have h0Fields := h0
  unfold Ω referenceRadialEndpointInvertibleLocus at h0Fields
  have hEnd : pR ∈ Ω := by simpa only [pR,one_mul] using hSegment 1 ⟨zero_le_one,le_rfl⟩
  have hDerivativeTransposeRaw := referenceAdjointHalfRadialFamily_deriv_zero_eq_transpose
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y h0
  have hDerivativeTranspose : deriv Ad 0 = sphereLowerDistributionalTranspose (deriv Dr 0) := by
    change deriv Ad 0 = sphereLowerDistributionalTranspose (deriv Dr 0) at hDerivativeTransposeRaw
    exact hDerivativeTransposeRaw
  have hDerivativePair (v z : Half) : Q v (deriv Ad 0 z) = Q z (deriv Dr 0 v) := by
    have hValue : deriv Ad 0 z = sphereLowerDistributionalTranspose (deriv Dr 0) z :=
      congrArg (fun T : Half →L[ℝ] Neg => T z) hDerivativeTranspose
    exact (congrArg (Q v) hValue).trans
      (sphereSobolevDualPairing_lower_distributionalTranspose (deriv Dr 0) v z).symm
  have hInc (v z : Half) : Q v (J z) = ⟪Z v,Z z⟫_ℝ := by
    have hFlip : Q v (J z) = sphereSobolevDualPairing (-(1/2 : ℝ)) (J z) v := by
      change ⟪v,J z⟫_ℝ = ⟪J z,v⟫_ℝ
      exact real_inner_comm (J z) v
    have hZero : sphereSobolevDualPairing (-(1/2 : ℝ)) (J z) v = ⟪Z z,Z v⟫_ℝ :=
      sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) z v
    exact hFlip.trans (hZero.trans (real_inner_comm (Z v) (Z z)))
  have hSCompat : ∀ v : Hi, Sl (I v) = J (Sh v) := by
    intro v
    have h := congrArg (fun A : Hi →L[ℝ] Neg => A v)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y (R y) hSegment)
    exact h.symm
  have hSTest (z : Half) (v : Hi) : Q (I v) (Tl z) = Q z (Sl (I v)) := by
    have hPivot : sphereSobolevDualPairing (-(1/2 : ℝ)) (Tl z) (I v) =
        ⟪Z z,Z (Sh v)⟫_ℝ :=
      (referenceRadialSecondRemainder_genuine_pivot_pairings
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) hSegment).2 z v
    have hSwap : Q (I v) (Tl z) = sphereSobolevDualPairing (-(1/2 : ℝ)) (Tl z) (I v) := by
      change ⟪I v,Tl z⟫_ℝ = ⟪Tl z,I v⟫_ℝ
      exact real_inner_comm (Tl z) (I v)
    exact hSwap.trans
      (hPivot.trans ((hInc z (Sh v)).symm.trans (congrArg (Q z) (hSCompat v).symm)))
  have hST (v z : Half) : Q v (Tl z) = Q z (Sl v) := by
    have hcLeft : Continuous (fun v : Half => Q v (Tl z)) := continuous_id.inner continuous_const
    have hcRight : Continuous (fun v : Half => Q z (Sl v)) := continuous_const.inner Sl.continuous
    have hAll := (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).equalizer
      hcLeft hcRight (funext (hSTest z))
    exact congrFun hAll v
  have hC (j : Fin 3) (v z : Half) : Q v (C0a j z) = Q z (C0d j v) :=
    (sphereSobolevDualPairing_referenceLowerCoordinateBoundary_adjoint g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p0 j h0Fields.2.1 v z).symm
  have hM (j : Fin 3) (v : Half) (z : Neg) : Q v (Ml j z) = Q (Mh j v) z :=
    sphereSobolevDualPairing_linearCoordinate_half_duality hF hO hD (EuclideanSpace.single j 1) z v
  have hN (j : Fin 3) (v : Half) (z : Neg) : Q v (Nl j z) = Q (Nh j v) z := by
    change ⟪v,nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j pR) z⟫_ℝ =
        ⟪Nh j v,z⟫_ℝ
    unfold nativeNegativeHalfCoefficientMulL
    change ⟪v,ContinuousLinearMap.adjoint (Nh j) z⟫_ℝ = ⟪Nh j v,z⟫_ℝ
    exact ContinuousLinearMap.adjoint_inner_right (Nh j) v z
  have hInterval : ∀ t ∈ uIcc (0 : ℝ) (R y), (q,(y,t)) ∈ Ω := by
    intro t ht
    have htSeg : t ∈ segment ℝ (0 : ℝ) (R y) := by simpa only [segment_eq_uIcc] using ht
    rcases htSeg with ⟨a,b,ha,hb,hab,heq⟩
    have hb1 : b ≤ 1 := by linarith only [ha,hab]
    have ht' : b*(R y) = t := by simpa only [smul_zero,zero_add,smul_eq_mul,mul_zero] using heq
    exact ht' ▸ hSegment b ⟨hb,hb1⟩
  have hNFamily (j : Fin 3) :
      referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j pR =
      referenceJacobiBoundaryCoefficientJets g hg L y0 Φ B ε C ρ H a w hData q y (R y) i j hInv :=
    referenceJacobiBoundaryCoefficientFamily_eq g hg L y0 Φ B ε C ρ H a w hData i j pR hInv
  have hOrdered := referenceLowerAdjointMovingDifferenceQuotient_eq_ordered_words
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq y hy R hR i hr hInv hInterval
  simp only [← hNFamily] at hOrdered
  change El = Tl.comp (Mh i) + (∑ j : Fin 3, (C0a j).comp (Nh j)) +
    R y • (∑ j : Fin 3, (deriv Ad 0).comp ((Mh j).comp (Nh j))) +
    (R y)^2 • (∑ j : Fin 3, Tl.comp ((Mh j).comp (Nh j))) +
    (R y*referenceRadiusHorizontalLogDerivative g L q R y i) • Tl at hOrdered
  have hLowerPair (v z : Half) : Q v (El z) = Q z (Ebl v) := by
    have h1 := (hST v (Mh i z)).trans (hM i z (Sl v)).symm
    have h2 (j : Fin 3) := (hC j v (Nh j z)).trans (hN j z (C0d j v)).symm
    have h3 (j : Fin 3) := (hDerivativePair v (Mh j (Nh j z))).trans
      ((hM j (Nh j z) (deriv Dr 0 v)).symm.trans (hN j z (Ml j (deriv Dr 0 v))).symm)
    have h4 (j : Fin 3) := (hST v (Mh j (Nh j z))).trans
      ((hM j (Nh j z) (Sl v)).symm.trans (hN j z (Ml j (Sl v))).symm)
    have h5 := hST v z
    have hPoint := congrArg (fun A : Half →L[ℝ] Neg => A z) hOrdered
    have hRewrite := congrArg (Q v) hPoint
    change Q v (El z) = Q z (referenceAdjointMovingDifferenceQuotientPivotLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i v)
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,Q,sphereSobolevDualPairing,
      inner_add_right,inner_sum,real_inner_smul_right] at hRewrite
    simp only [Q,sphereSobolevDualPairing] at h1 h2 h3 h4 h5
    unfold referenceAdjointMovingDifferenceQuotientPivotLow
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,Q,sphereSobolevDualPairing,
      inner_add_right,inner_sum,real_inner_smul_right]
    exact hRewrite.trans (congrArg₂ (fun a b : ℝ => a+b)
      (congrArg₂ (fun a b : ℝ => a+b)
        (congrArg₂ (fun a b : ℝ => a+b)
          (congrArg₂ (fun a b : ℝ => a+b) h1 (Finset.sum_congr rfl (fun j _ => h2 j)))
          (congrArg (fun t : ℝ => R y*t) (Finset.sum_congr rfl (fun j _ => h3 j))))
        (congrArg (fun t : ℝ => (R y)^2*t) (Finset.sum_congr rfl (fun j _ => h4 j))))
      (congrArg (fun t : ℝ => (R y*referenceRadiusHorizontalLogDerivative g L q R y i)*t) h5))
  have hBar := congrArg (fun A : Hi →L[ℝ] Neg => A u)
    (referenceAdjointMovingDifferenceQuotientPivot_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR y hy hr hInv hSegment i)
  have hActual := congrArg (fun A : Hi →L[ℝ] Neg => A u)
    (referenceAdjointMovingDifferenceQuotient_high_lower_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R y hy i hInv hEnd)
  constructor
  · exact (hLowerPair (I u) z).trans ((congrArg (Q z) hBar.symm).trans (hInc z _))
  · exact (hLowerPair z (I u)).symm.trans ((congrArg (Q z) hActual.symm).trans (hInc z _))

lemma contDiffOn_referenceAdjointMovingDifferenceQuotientPivot
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (q : ℝ)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R) :
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let U : Set R3 := {y | R y ≠ 0 ∧
      (∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*R y)) ∈ Ω) ∧
      (∀ ξ : UnitSphere,
        (referenceFramedNormalizedJacobian g L Φ (q,((y,R y),ξ.val))).IsInvertible)}
    ∀ i : Fin 3,
      ContDiffOn ℝ ∞ (fun y : R3 => referenceAdjointMovingDifferenceQuotientPivotHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U ∧
      ContDiffOn ℝ ∞ (fun y : R3 => referenceAdjointMovingDifferenceQuotientPivotLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) U := by
  intro Ω U i
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let χ : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,R x))
  let χ0 : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,0))
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.prodMk (contDiff_id.prodMk hR)
  have hχ0 : ContDiff ℝ ∞ χ0 := contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hDh : ContDiffOn ℝ ∞
      (fun z : ℝ × (R3 × ℝ) => deriv (fun t : ℝ => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2) Ω :=
    contDiffOn_deriv_joint_radialSlice
      (fun z => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z) Ω hΩ
      (contDiffOn_referenceSharpRadialTraceFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
  have hDl : ContDiffOn ℝ ∞
      (fun z : ℝ × (R3 × ℝ) => deriv (fun t : ℝ => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2) Ω :=
    contDiffOn_deriv_joint_radialSlice
      (fun z => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z) Ω hΩ
      (contDiffOn_referenceLowerRadialEndpointFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
  constructor
  · intro y hy
    have h0 : (q,(y,0)) ∈ Ω := by
      simpa only [zero_mul] using hy.2.1 0 ⟨le_rfl,zero_le_one⟩
    have h0Fields := h0
    unfold Ω referenceRadialEndpointInvertibleLocus at h0Fields
    have hS : ContDiffAt ℝ ∞ (fun x : R3 => referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q x (R x)) y :=
      ContDiffAt.fun_comp (f := χ)
        (g := fun z : ℝ × (R3 × ℝ) => referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2) y
        ((contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) hy.2.1).1) hχ.contDiffAt
    have hC (j : Fin 3) : ContDiffAt ℝ ∞ (fun x : R3 => referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,0)) j) y :=
      ContDiffAt.fun_comp (f := χ0)
        (g := fun z : ℝ × (R3 × ℝ) => referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j) y
        (contDiffAt_referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j h0Fields.1) hχ0.contDiffAt
    have hDerivative : ContDiffAt ℝ ∞
        (fun x : R3 => deriv (fun t : ℝ => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,t))) 0) y :=
      ContDiffAt.fun_comp (f := χ0)
        (g := fun z : ℝ × (R3 × ℝ) => deriv
          (fun t : ℝ => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2) y
        (hDh.contDiffAt (hΩ.mem_nhds h0)) hχ0.contDiffAt
    have hN (j : Fin 3) : ContDiffAt ℝ ∞
        (fun x : R3 => nativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j (q,(x,R x)))) y :=
      ContDiffAt.fun_comp (f := χ)
        (g := fun z : ℝ × (R3 × ℝ) => nativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j z)) y
        (contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,R y)) hy.2.2) hχ.contDiffAt
    have hf : ContDiffAt ℝ ∞ (fun x : R3 => referenceRadiusHorizontalLogDerivative g L q R x i) y :=
      (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i hR.contDiffAt hy.1).comp y
        (contDiffAt_const.prodMk contDiffAt_id)
    have hM (j : Fin 3) : ContDiffAt ℝ ∞
        (fun _ : R3 => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)) y := contDiffAt_const
    have hFirst := (hM i).clm_comp hS
    have hSecond := ContDiffAt.sum (s := Finset.univ) (fun j _ => (hN j).clm_comp (hC j))
    have hThird := hR.contDiffAt.smul
      (ContDiffAt.sum (s := Finset.univ) (fun j _ => (hN j).clm_comp ((hM j).clm_comp hDerivative)))
    have hFourth := (hR.contDiffAt.pow 2).smul
      (ContDiffAt.sum (s := Finset.univ) (fun j _ => (hN j).clm_comp ((hM j).clm_comp hS)))
    have hFifth := (hR.contDiffAt.mul hf).smul hS
    exact (by
      simpa only [referenceAdjointMovingDifferenceQuotientPivotHigh,Pi.smul_apply',Function.comp_apply] using
        ((((hFirst.add hSecond).add hThird).add hFourth).add hFifth).contDiffWithinAt)
  · intro y hy
    have h0 : (q,(y,0)) ∈ Ω := by
      simpa only [zero_mul] using hy.2.1 0 ⟨le_rfl,zero_le_one⟩
    have h0Fields := h0
    unfold Ω referenceRadialEndpointInvertibleLocus at h0Fields
    have hS : ContDiffAt ℝ ∞ (fun x : R3 => referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q x (R x)) y :=
      ContDiffAt.fun_comp (f := χ)
        (g := fun z : ℝ × (R3 × ℝ) => referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2) y
        ((contDiffAt_referencePairedRadialSecondRemainder_low_input_families_of_segment
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) hy.2.1).1) hχ.contDiffAt
    have hC (j : Fin 3) : ContDiffAt ℝ ∞ (fun x : R3 => referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,0)) j) y :=
      ContDiffAt.fun_comp (f := χ0)
        (g := fun z : ℝ × (R3 × ℝ) => referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j) y
        (contDiffAt_referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j h0Fields.2.2 h0Fields.2.1) hχ0.contDiffAt
    have hDerivative : ContDiffAt ℝ ∞
        (fun x : R3 => deriv (fun t : ℝ => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(x,t))) 0) y :=
      ContDiffAt.fun_comp (f := χ0)
        (g := fun z : ℝ × (R3 × ℝ) => deriv
          (fun t : ℝ => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2) y
        (hDl.contDiffAt (hΩ.mem_nhds h0)) hχ0.contDiffAt
    have hN (j : Fin 3) : ContDiffAt ℝ ∞
        (fun x : R3 => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j (q,(x,R x)))) y :=
      ContDiffAt.fun_comp (f := χ)
        (g := fun z : ℝ × (R3 × ℝ) => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
          (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j z)) y
        (contDiffAt_nativeNegativeHalf_referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,R y)) hy.2.2) hχ.contDiffAt
    have hf : ContDiffAt ℝ ∞ (fun x : R3 => referenceRadiusHorizontalLogDerivative g L q R x i) y :=
      (contDiffAt_referenceRadiusHorizontalLogDerivative g L hg R (q,y) i hR.contDiffAt hy.1).comp y
        (contDiffAt_const.prodMk contDiffAt_id)
    have hM (j : Fin 3) : ContDiffAt ℝ ∞
        (fun _ : R3 => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)) y := contDiffAt_const
    have hFirst := (hM i).clm_comp hS
    have hSecond := ContDiffAt.sum (s := Finset.univ) (fun j _ => (hN j).clm_comp (hC j))
    have hThird := hR.contDiffAt.smul
      (ContDiffAt.sum (s := Finset.univ) (fun j _ => (hN j).clm_comp ((hM j).clm_comp hDerivative)))
    have hFourth := (hR.contDiffAt.pow 2).smul
      (ContDiffAt.sum (s := Finset.univ) (fun j _ => (hN j).clm_comp ((hM j).clm_comp hS)))
    have hFifth := (hR.contDiffAt.mul hf).smul hS
    exact (by
      simpa only [referenceAdjointMovingDifferenceQuotientPivotLow,Pi.smul_apply',Function.comp_apply] using
        ((((hFirst.add hSecond).add hThird).add hFourth).add hFifth).contDiffWithinAt)

lemma norm_coordinateFieldWordPartial_reversed_clm_sum_le
    {E V : Type 0} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (power : ℕ) (Ta Tnext D : R3 → E →L[ℝ] V) (C0 : Fin 3 → R3 → E →L[ℝ] V)
    (Na Nnext Ntwo : Fin 3 → R3 → V →L[ℝ] V) (M : Fin 3 → V →L[ℝ] V)
    (f : R3 → ℝ) (i : Fin 3) (U : Set R3) (hU : IsOpen U)
    (hTa : ContDiffOn ℝ ∞ Ta U) (hTnext : ContDiffOn ℝ ∞ Tnext U)
    (hD : ContDiffOn ℝ ∞ D U) (hC0 : ∀ j, ContDiffOn ℝ ∞ (C0 j) U)
    (hNa : ∀ j, ContDiffOn ℝ ∞ (Na j) U)
    (hNnext : ∀ j, ContDiffOn ℝ ∞ (Nnext j) U)
    (hNtwo : ∀ j, ContDiffOn ℝ ∞ (Ntwo j) U)
    (hf : ContDiffOn ℝ ∞ f U) (x : R3) (hx : x ∈ U)
    (C B F m beta eta : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hm : ∀ j, ‖M j‖ ≤ m) (hbeta : 1 ≤ beta) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hTaB : HasCoordinateWordJetBound 3 Ta x (C*eta^power/beta^(2*power)) beta 0)
    (hTnextB : HasCoordinateWordJetBound 3 Tnext x (C*eta^(power+1)/beta^(2*(power+1))) beta 0)
    (hDB : HasCoordinateWordJetBound 3 D x B beta 0)
    (hC0B : ∀ j, HasCoordinateWordJetBound 3 (C0 j) x B beta 0)
    (hNaB : ∀ j, HasCoordinateWordJetBound 3 (Na j) x (C*eta^power/beta^(2*power)) beta 0)
    (hNnextB : ∀ j, HasCoordinateWordJetBound 3 (Nnext j) x (C*eta^(power+1)/beta^(2*(power+1))) beta 0)
    (hNtwoB : ∀ j, HasCoordinateWordJetBound 3 (Ntwo j) x (C*eta^2/beta^4) beta 0)
    (hfB : HasCoordinateWordJetBound 3 f x F beta 1)
    (word : List (Fin 3)) (hw : word.length ≤ 3) :
    ‖coordinateFieldWordPartial word (fun y =>
      (M i).comp (Ta y) + (∑ j : Fin 3, (Na j y).comp (C0 j y)) +
      (∑ j : Fin 3, (Nnext j y).comp ((M j).comp (D y))) +
      (∑ j : Fin 3, (Ntwo j y).comp ((M j).comp (Ta y))) +
      f y • Tnext y) x‖ ≤
      (C*m+24*B*C+24*B*m*C+24*C^2*m+8*F*C)*eta^power*beta^word.length/beta^(2*power) := by
  classical
  have hm0 : 0 ≤ m := (norm_nonneg (M i)).trans (hm i)
  have hb0 : 0 ≤ beta := (by norm_num : (0 : ℝ) ≤ 1).trans hbeta
  have hbp : 0 < beta := lt_of_lt_of_le zero_lt_one hbeta
  let a : ℝ := C*eta^power/beta^(2*power)
  let b : ℝ := C*eta^(power+1)/beta^(2*(power+1))
  let c : ℝ := C*eta^2/beta^4
  have hc : 0 ≤ c := div_nonneg (mul_nonneg hC (sq_nonneg eta)) (pow_nonneg hb0 _)
  have ha : 0 ≤ a := div_nonneg (mul_nonneg hC (pow_nonneg heta _)) (pow_nonneg hb0 _)
  have hb : 0 ≤ b := div_nonneg (mul_nonneg hC (pow_nonneg heta _)) (pow_nonneg hb0 _)
  let left : Fin 3 → (E →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) := fun j =>
    ContinuousLinearMap.compL ℝ E V V (M j)
  have hLeft (j : Fin 3) : ‖left j‖ ≤ m := by
    apply ContinuousLinearMap.opNorm_le_bound (left j) hm0
    intro A
    change ‖(M j).comp A‖ ≤ m * ‖A‖
    exact ((M j).opNorm_comp_le A).trans
      (mul_le_mul_of_nonneg_right (hm j) (norm_nonneg A))
  have hMTa (j : Fin 3) := hasCoordinateWordJetBound_fixed_map_of_isOpen
    (left j) 3 Ta U hU hTa x hx m a beta 0 (hLeft j) hTaB
  have hMD (j : Fin 3) := hasCoordinateWordJetBound_fixed_map_of_isOpen
    (left j) 3 D U hU hD x hx m B beta 0 (hLeft j) hDB
  have hOne := hMTa i
  have hTwo (j : Fin 3) := hasCoordinateWordJetBound_clm_comp_of_isOpen
    3 (Na j) (C0 j) U hU (hNa j) (hC0 j) x hx a B beta 0 0 ha hB hb0 (hNaB j) (hC0B j)
  have hThree (j : Fin 3) := hasCoordinateWordJetBound_clm_comp_of_isOpen
    3 (Nnext j) (fun y => (M j).comp (D y)) U hU (hNnext j)
    (contDiffOn_const.clm_comp hD) x hx b (m*B) beta 0 0
    hb (mul_nonneg hm0 hB) hb0 (hNnextB j) (hMD j)
  have hFour (j : Fin 3) := hasCoordinateWordJetBound_clm_comp_of_isOpen
    3 (Ntwo j) (fun y => (M j).comp (Ta y)) U hU (hNtwo j)
    (contDiffOn_const.clm_comp hTa) x hx c (m*a) beta 0 0
    hc (mul_nonneg hm0 ha) hb0 (hNtwoB j) (hMTa j)
  have hFive := hasCoordinateWordJetBound_smul_of_isOpen
    3 f Tnext U hU hf hTnext x hx F b beta 1 0 hF hb hb0 hfB hTnextB
  have hFive0 : HasCoordinateWordJetBound 3 (fun y => f y • Tnext y) x
      (((2:ℝ)^3*F*b)*beta) beta 0 := by
    intro w hw
    have h := hFive w hw
    have heq : ((2:ℝ)^3*F*b)*beta^(1+w.length) =
        (((2:ℝ)^3*F*b)*beta)*beta^(0+w.length) := by
      rw [zero_add,pow_add,pow_one]
      ring
    exact h.trans_eq heq
  have hSum2 := hasCoordinateWordJetBound_sum_of_isOpen
    3 (fun j y => (Na j y).comp (C0 j y)) U hU
    (fun j => (hNa j).clm_comp (hC0 j)) x hx ((2:ℝ)^3*a*B) beta 0 hTwo
  have hSum3 := hasCoordinateWordJetBound_sum_of_isOpen
    3 (fun j y => (Nnext j y).comp ((M j).comp (D y))) U hU
    (fun j => (hNnext j).clm_comp (contDiffOn_const.clm_comp hD))
    x hx ((2:ℝ)^3*b*(m*B)) beta 0 hThree
  have hSum4 := hasCoordinateWordJetBound_sum_of_isOpen
    3 (fun j y => (Ntwo j y).comp ((M j).comp (Ta y))) U hU
    (fun j => (hNtwo j).clm_comp (contDiffOn_const.clm_comp hTa))
    x hx ((2:ℝ)^3*c*(m*a)) beta 0 hFour
  have hs1 : ContDiffOn ℝ ∞ (fun y => (M i).comp (Ta y)) U :=
    contDiffOn_const.clm_comp hTa
  have hs2 : ContDiffOn ℝ ∞ (fun y => ∑ j : Fin 3, (Na j y).comp (C0 j y)) U :=
    ContDiffOn.sum (fun j _ => (hNa j).clm_comp (hC0 j))
  have hs3 : ContDiffOn ℝ ∞ (fun y => ∑ j : Fin 3, (Nnext j y).comp ((M j).comp (D y))) U :=
    ContDiffOn.sum (fun j _ => (hNnext j).clm_comp (contDiffOn_const.clm_comp hD))
  have hs4 : ContDiffOn ℝ ∞ (fun y => ∑ j : Fin 3, (Ntwo j y).comp ((M j).comp (Ta y))) U :=
    ContDiffOn.sum (fun j _ => (hNtwo j).clm_comp (contDiffOn_const.clm_comp hTa))
  have h12 := hasCoordinateWordJetBound_add_of_isOpen 3 _ _ U hU hs1 hs2 x hx _ _ beta 0 hOne hSum2
  have h123 := hasCoordinateWordJetBound_add_of_isOpen 3 _ _ U hU (hs1.add hs2) hs3 x hx _ _ beta 0 h12 hSum3
  have h1234 := hasCoordinateWordJetBound_add_of_isOpen 3 _ _ U hU ((hs1.add hs2).add hs3) hs4 x hx _ _ beta 0 h123 hSum4
  have hAll := hasCoordinateWordJetBound_add_of_isOpen 3 _ _ U hU (((hs1.add hs2).add hs3).add hs4)
    (hf.smul hTnext) x hx _ _ beta 0 h1234 hFive0
  have hBeta2 : 1 ≤ beta^2 := one_le_pow₀ hbeta
  have hEtaBeta : eta ≤ beta := heta1.trans hbeta
  have hEtaBeta2 : eta ≤ beta^2 := heta1.trans hBeta2
  have hRatio1 : eta/beta ≤ 1 := (div_le_one hbp).mpr hEtaBeta
  have hRatio2 : eta/beta^2 ≤ 1 := (div_le_one (pow_pos hbp 2)).mpr hEtaBeta2
  have hRatio20 : 0 ≤ eta/beta^2 := div_nonneg heta (pow_nonneg hb0 _)
  have hRatioSq : (eta/beta^2)^2 ≤ 1 := pow_le_one₀ hRatio20 hRatio2
  have hBFactor : b = a*(eta/beta^2) := by
    dsimp only [a,b]
    rw [show 2*(power+1) = 2*power+2 by omega,pow_add,pow_succ]
    field_simp [ne_of_gt hbp]
    <;> ring
  have hBBetaFactor : b*beta = a*(eta/beta) := by
    rw [hBFactor]
    field_simp [ne_of_gt hbp]
    <;> ring
  have hCFactor : c = C*(eta/beta^2)^2 := by
    dsimp only [c]
    field_simp [ne_of_gt hbp]
    <;> ring
  have hBLe : b ≤ a := by
    rw [hBFactor]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRatio2 ha
  have hBBetaLe : b*beta ≤ a := by
    rw [hBBetaFactor]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRatio1 ha
  have hCLe : c ≤ C := by
    rw [hCFactor]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRatioSq hC
  have hThreeLe : 24*B*(m*b) ≤ 24*B*m*a := by
    nlinarith only [mul_le_mul_of_nonneg_left hBLe
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤24) hB) hm0)]
  have hFourLe : 24*a*(m*c) ≤ 24*C*m*a := by
    nlinarith only [mul_le_mul_of_nonneg_left hCLe
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤24) ha) hm0)]
  have hFiveLe : 8*F*b*beta ≤ 8*F*a := by
    nlinarith only [mul_le_mul_of_nonneg_left hBBetaLe
      (mul_nonneg (by norm_num : (0:ℝ)≤8) hF)]
  have hCoeff : m*a+24*B*a+24*B*(m*b)+24*a*(m*c)+8*F*b*beta ≤
      (m+24*B+24*B*m+24*C*m+8*F)*a := by
    nlinarith only [hThreeLe,hFourLe,hFiveLe]
  have hFinal := hAll word hw
  norm_num only [Fintype.card_fin,Nat.cast_ofNat,pow_succ,pow_zero,zero_add] at hFinal
  calc
    _ ≤ (m*a+24*B*a+24*B*(m*b)+24*a*(m*c)+8*F*b*beta)*beta^word.length := by
      convert hFinal using 1 <;> ring
    _ ≤ ((m+24*B+24*B*m+24*C*m+8*F)*a)*beta^word.length :=
      mul_le_mul_of_nonneg_right hCoeff (pow_nonneg hb0 _)
    _ = (C*m+24*B*C+24*B*m*C+24*C^2*m+8*F*C)*eta^power*beta^word.length/beta^(2*power) := by
      dsimp only [a]
      ring

lemma exists_referenceBoundary_static_zero_radial_coordinate_word_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (dGeom : ℝ) (hdGeom : 0 < dGeom)
    (hRoom : Set.prod (Icc (0 : ℝ) 1)
      (Set.prod (Metric.closedBall y0 ρ) (Icc (-dGeom) dGeom)) ⊆
        referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    let Ch : Fin 3 → (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun j z =>
      referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j
    let Dh : (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun z =>
      deriv (fun t : ℝ => referenceSharpRadialTraceFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let Cl : Fin 3 → (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun j z =>
      referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j
    let Dl : (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun z =>
      deriv (fun t : ℝ => referenceLowerRadialEndpointFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    ∃ Bh Bl : ℝ, 0 ≤ Bh ∧ 0 ≤ Bl ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ Metric.closedBall y0 ρ,
        ∀ beta : ℝ, 1 ≤ beta → ∀ i : Fin 3,
          HasCoordinateWordJetBound 3 (fun y => Ch i (q,(y,0))) x Bh beta 0 ∧
          HasCoordinateWordJetBound 3 (fun y => Dh (q,(y,0))) x Bh beta 0 ∧
          HasCoordinateWordJetBound 3 (fun y => Cl i (q,(y,0))) x Bl beta 0 ∧
          HasCoordinateWordJetBound 3 (fun y => Dl (q,(y,0))) x Bl beta 0 := by
  classical
  dsimp only
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let Kg : Set (ℝ × (R3 × ℝ)) := Set.prod (Icc (0 : ℝ) 1) (Set.prod (closedBall y0 ρ) (Icc (-dGeom) dGeom))
  have hKg : IsCompact Kg := isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hKgΩ : Kg ⊆ Ω := hRoom
  let Ch : Fin 3 → (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun j z => referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j
  let Dh : (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun z =>
    deriv (fun t : ℝ => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
  have hChOn (j : Fin 3) : ContDiffOn ℝ ∞ (Ch j) Ω := by
    intro z hz
    have hzFields := hz
    unfold Ω referenceRadialEndpointInvertibleLocus at hzFields
    exact (contDiffAt_referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j hzFields.1).contDiffWithinAt
  have hDhOn : ContDiffOn ℝ ∞ Dh Ω :=
    contDiffOn_deriv_joint_radialSlice (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) Ω hΩ
      (contDiffOn_referenceSharpRadialTraceFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
  have hStatich := exists_compact_finite_pair_iteratedFDeriv_bound
    (fun i (_ : Fin 3) z => Ch i z) (fun (_ _ : Fin 3) z => Dh z) Kg hKg
    (fun i _ z hz => (hChOn i).contDiffAt (hΩ.mem_nhds (hKgΩ hz)))
    (fun _ _ z hz => hDhOn.contDiffAt (hΩ.mem_nhds (hKgΩ hz))) 3
  rcases hStatich with ⟨Bh,hBh,hBoundh⟩
  have hStatichWord (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (x : R3) (hx : x ∈ closedBall y0 ρ)
      (beta : ℝ) (hbeta : 1 ≤ beta) (i : Fin 3) :
      HasCoordinateWordJetBound 3 (fun y => Ch i (q,(y,0))) x Bh beta 0 ∧
      HasCoordinateWordJetBound 3 (fun y => Dh (q,(y,0))) x Bh beta 0 := by
    have hz : (q,(x,(0 : ℝ))) ∈ Kg := ⟨hq,hx,⟨neg_nonpos.mpr hdGeom.le,hdGeom.le⟩⟩
    constructor
    · intro word hw
      have h1 := norm_coordinateFieldWordPartial_joint_slice_le word (Ch i) Ω hΩ (hChOn i) q 0 x (hKgΩ hz)
      have h2 := (hBoundh (q,(x,0)) hz i (0 : Fin 3) word.length hw).1
      have hScalar : Bh * 1 ≤ Bh * beta ^ word.length :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hbeta) hBh
      exact (h1.trans h2).trans (by
        simpa only [Nat.zero_add,mul_one] using hScalar)
    · intro word hw
      have h1 := norm_coordinateFieldWordPartial_joint_slice_le word Dh Ω hΩ hDhOn q 0 x (hKgΩ hz)
      have h2 := (hBoundh (q,(x,0)) hz i (0 : Fin 3) word.length hw).2
      have hScalar : Bh * 1 ≤ Bh * beta ^ word.length :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hbeta) hBh
      exact (h1.trans h2).trans (by
        simpa only [Nat.zero_add,mul_one] using hScalar)
  let Cl : Fin 3 → (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun j z => referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j
  let Dl : (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun z =>
    deriv (fun t : ℝ => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
  have hClOn (j : Fin 3) : ContDiffOn ℝ ∞ (Cl j) Ω := by
    intro z hz
    have hzFields := hz
    unfold Ω referenceRadialEndpointInvertibleLocus at hzFields
    exact (contDiffAt_referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j hzFields.2.2 hzFields.2.1).contDiffWithinAt
  have hDlOn : ContDiffOn ℝ ∞ Dl Ω :=
    contDiffOn_deriv_joint_radialSlice (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) Ω hΩ
      (contDiffOn_referenceLowerRadialEndpointFamily_invertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
  have hStaticl := exists_compact_finite_pair_iteratedFDeriv_bound
    (fun i (_ : Fin 3) z => Cl i z) (fun (_ _ : Fin 3) z => Dl z) Kg hKg
    (fun i _ z hz => (hClOn i).contDiffAt (hΩ.mem_nhds (hKgΩ hz)))
    (fun _ _ z hz => hDlOn.contDiffAt (hΩ.mem_nhds (hKgΩ hz))) 3
  rcases hStaticl with ⟨Bl,hBl,hBoundl⟩
  have hStaticlWord (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (x : R3) (hx : x ∈ closedBall y0 ρ)
      (beta : ℝ) (hbeta : 1 ≤ beta) (i : Fin 3) :
      HasCoordinateWordJetBound 3 (fun y => Cl i (q,(y,0))) x Bl beta 0 ∧
      HasCoordinateWordJetBound 3 (fun y => Dl (q,(y,0))) x Bl beta 0 := by
    have hz : (q,(x,(0 : ℝ))) ∈ Kg := ⟨hq,hx,⟨neg_nonpos.mpr hdGeom.le,hdGeom.le⟩⟩
    constructor
    · intro word hw
      have h1 := norm_coordinateFieldWordPartial_joint_slice_le word (Cl i) Ω hΩ (hClOn i) q 0 x (hKgΩ hz)
      have h2 := (hBoundl (q,(x,0)) hz i (0 : Fin 3) word.length hw).1
      have hScalar : Bl * 1 ≤ Bl * beta ^ word.length :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hbeta) hBl
      exact (h1.trans h2).trans (by
        simpa only [Nat.zero_add,mul_one] using hScalar)
    · intro word hw
      have h1 := norm_coordinateFieldWordPartial_joint_slice_le word Dl Ω hΩ hDlOn q 0 x (hKgΩ hz)
      have h2 := (hBoundl (q,(x,0)) hz i (0 : Fin 3) word.length hw).2
      have hScalar : Bl * 1 ≤ Bl * beta ^ word.length :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hbeta) hBl
      exact (h1.trans h2).trans (by
        simpa only [Nat.zero_add,mul_one] using hScalar)
  refine ⟨Bh,Bl,hBh,hBl,?_⟩
  intro q hq x hx beta hbeta i
  have hHigh := hStatichWord q hq x hx beta hbeta i
  have hLow := hStaticlWord q hq x hx beta hbeta i
  exact ⟨hHigh.1,hHigh.2,hLow.1,hLow.2⟩

lemma referencePairedRadialJacobi_profile_high_coordinate_word_data
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (x : R3) (Cscaled eta beta : ℝ) :
    let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let SegΩ : Set (ℝ × (R3 × ℝ)) :=
      {z | ∀ θ ∈ Icc (0 : ℝ) 1, (z.1,(z.2.1,θ*z.2.2)) ∈ Ω}
    let V : Set (ℝ × (R3 × ℝ)) := {z | ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible}
    let χ : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
    let U : Set R3 := {y | R y ≠ 0 ∧ χ y ∈ SegΩ ∧ χ y ∈ V}
    let S : (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun z =>
      referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let N : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → Half →L[ℝ] Half := fun i j z =>
      nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j z)
    let C0 : Fin 3 → R3 → Hi →L[ℝ] Half := fun j y =>
      referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let D0 : R3 → Hi →L[ℝ] Half := fun y =>
      deriv (fun t : ℝ => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    x ∈ U →
    (∀ radiusPower : ℕ, 1 ≤ radiusPower → radiusPower ≤ 3 →
      ∀ order : ℕ, order ≤ 3 →
        ‖iteratedFDeriv ℝ order (fun y : R3 => ((1 : ℝ)*R y)^radiusPower •
          S (q,(y,(1 : ℝ)*R y))) x‖ ≤ Cscaled*eta^radiusPower*beta^order/beta^(2*radiusPower) ∧
        ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ order (fun y : R3 => ((1 : ℝ)*R y)^radiusPower •
          N i j (q,(y,(1 : ℝ)*R y))) x‖ ≤ Cscaled*eta^radiusPower*beta^order/beta^(2*radiusPower)) →
    (∀ radiusPower : ℕ, ContDiffOn ℝ ∞
      (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) U) ∧
    (∀ radiusPower : ℕ, ∀ i j : Fin 3, ContDiffOn ℝ ∞
      (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) U) ∧
    (∀ j : Fin 3, ContDiffOn ℝ ∞ (C0 j) U) ∧
    ContDiffOn ℝ ∞ D0 U ∧
    ∀ radiusPower : ℕ, 1 ≤ radiusPower → radiusPower ≤ 3 →
      HasCoordinateWordJetBound 3
        (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) x
        (Cscaled*eta^radiusPower/beta^(2*radiusPower)) beta 0 ∧
      ∀ i j : Fin 3, HasCoordinateWordJetBound 3
        (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) x
        (Cscaled*eta^radiusPower/beta^(2*radiusPower)) beta 0 := by
  intro Ω SegΩ V χ U S N C0 D0 hxU hRaw
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.prodMk (contDiff_id.prodMk hR)
  have hχ0 : ContDiff ℝ ∞ (fun y : R3 => (q,(y,(0 : ℝ)))) :=
    contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hOpen := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hU : IsOpen U := hOpen.1
  have hSOn (radiusPower : ℕ) : ContDiffOn ℝ ∞
      (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) U := by
    intro y hy
    have hS := ContDiffAt.fun_comp (f := χ) (g := S) y
      ((contDiffAt_referencePairedRadialSecondRemainder_high_input_families_of_segment
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) hy.2.1).1)
      hχ.contDiffAt
    exact ((hR.contDiffAt.pow radiusPower).smul hS).contDiffWithinAt
  have hNOn (radiusPower : ℕ) (i j : Fin 3) : ContDiffOn ℝ ∞
      (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) U := by
    intro y hy
    have hN := ContDiffAt.fun_comp (f := χ) (g := N i j) y
      (contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (χ y) hy.2.2)
      hχ.contDiffAt
    exact ((hR.contDiffAt.pow radiusPower).smul hN).contDiffWithinAt
  have hC0On (j : Fin 3) : ContDiffOn ℝ ∞ (C0 j) U := by
    intro y hy
    have h0 : (q,(y,0)) ∈ Ω := by
      simpa only [zero_mul] using hy.2.1 0 ⟨le_rfl,zero_le_one⟩
    have hzFields := h0
    unfold Ω referenceRadialEndpointInvertibleLocus at hzFields
    have hC := contDiffAt_referenceHighCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j hzFields.1
    exact (ContDiffAt.fun_comp (f := fun y : R3 => (q,(y,(0 : ℝ))))
      (g := fun z : ℝ × (R3 × ℝ) => referenceHighCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j) y hC hχ0.contDiffAt).contDiffWithinAt
  let Dj : (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun z =>
    deriv (fun t : ℝ => referenceSharpRadialTraceFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
  have hDj : ContDiffOn ℝ ∞ Dj Ω :=
    contDiffOn_deriv_joint_radialSlice
      (referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) Ω hΩ
      (contDiffOn_referenceSharpRadialTraceFamily_invertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
  have hD0On : ContDiffOn ℝ ∞ D0 U := by
    intro y hy
    have h0 : (q,(y,0)) ∈ Ω := by
      simpa only [zero_mul] using hy.2.1 0 ⟨le_rfl,zero_le_one⟩
    change ContDiffWithinAt ℝ ∞ (fun y : R3 => Dj (q,(y,0))) U y
    exact (ContDiffAt.fun_comp (f := fun y : R3 => (q,(y,(0 : ℝ))))
      (g := Dj) y (hDj.contDiffAt (hΩ.mem_nhds h0)) hχ0.contDiffAt).contDiffWithinAt
  have hSBound (radiusPower : ℕ) (ha1 : 1 ≤ radiusPower) (ha3 : radiusPower ≤ 3) :
      HasCoordinateWordJetBound 3
        (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) x
        (Cscaled*eta^radiusPower/beta^(2*radiusPower)) beta 0 := by
    intro word hw
    have hActual := hRaw radiusPower ha1 ha3 word.length hw
    have hJet : ‖iteratedFDeriv ℝ word.length
        (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) x‖ ≤
          Cscaled*eta^radiusPower*beta^word.length/beta^(2*radiusPower) := by
      simpa only [one_mul] using hActual.1
    calc
      _ ≤ ‖iteratedFDeriv ℝ word.length
          (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) x‖ :=
        norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen word _ U hU (hSOn radiusPower) x hxU
      _ ≤ Cscaled*eta^radiusPower*beta^word.length/beta^(2*radiusPower) := hJet
      _ = (Cscaled*eta^radiusPower/beta^(2*radiusPower))*beta^(0+word.length) := by
        simp only [Nat.zero_add]; ring
  have hNBound (radiusPower : ℕ) (ha1 : 1 ≤ radiusPower) (ha3 : radiusPower ≤ 3) (i j : Fin 3) :
      HasCoordinateWordJetBound 3
        (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) x
        (Cscaled*eta^radiusPower/beta^(2*radiusPower)) beta 0 := by
    intro word hw
    have hActual := hRaw radiusPower ha1 ha3 word.length hw
    have hJet : ‖iteratedFDeriv ℝ word.length
        (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) x‖ ≤
          Cscaled*eta^radiusPower*beta^word.length/beta^(2*radiusPower) := by
      simpa only [one_mul] using hActual.2 i j
    calc
      _ ≤ ‖iteratedFDeriv ℝ word.length
          (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) x‖ :=
        norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen word _ U hU (hNOn radiusPower i j) x hxU
      _ ≤ Cscaled*eta^radiusPower*beta^word.length/beta^(2*radiusPower) := hJet
      _ = (Cscaled*eta^radiusPower/beta^(2*radiusPower))*beta^(0+word.length) := by
        simp only [Nat.zero_add]; ring
  exact ⟨hSOn,hNOn,hC0On,hD0On,fun a ha1 ha3 =>
    ⟨hSBound a ha1 ha3,fun i j => hNBound a ha1 ha3 i j⟩⟩

lemma referencePairedRadialJacobi_profile_low_coordinate_word_data
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (x : R3) (Cscaled eta beta : ℝ) :
    let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let SegΩ : Set (ℝ × (R3 × ℝ)) :=
      {z | ∀ θ ∈ Icc (0 : ℝ) 1, (z.1,(z.2.1,θ*z.2.2)) ∈ Ω}
    let V : Set (ℝ × (R3 × ℝ)) := {z | ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible}
    let χ : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
    let U : Set R3 := {y | R y ≠ 0 ∧ χ y ∈ SegΩ ∧ χ y ∈ V}
    let S : (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun z =>
      referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let N : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → Neg →L[ℝ] Neg := fun i j z =>
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j z)
    let C0 : Fin 3 → R3 → Half →L[ℝ] Neg := fun j y =>
      referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let D0 : R3 → Half →L[ℝ] Neg := fun y =>
      deriv (fun t : ℝ => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    x ∈ U →
    (∀ radiusPower : ℕ, 1 ≤ radiusPower → radiusPower ≤ 3 →
      ∀ order : ℕ, order ≤ 3 →
        ‖iteratedFDeriv ℝ order (fun y : R3 => ((1 : ℝ)*R y)^radiusPower •
          S (q,(y,(1 : ℝ)*R y))) x‖ ≤ Cscaled*eta^radiusPower*beta^order/beta^(2*radiusPower) ∧
        ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ order (fun y : R3 => ((1 : ℝ)*R y)^radiusPower •
          N i j (q,(y,(1 : ℝ)*R y))) x‖ ≤ Cscaled*eta^radiusPower*beta^order/beta^(2*radiusPower)) →
    (∀ radiusPower : ℕ, ContDiffOn ℝ ∞
      (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) U) ∧
    (∀ radiusPower : ℕ, ∀ i j : Fin 3, ContDiffOn ℝ ∞
      (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) U) ∧
    (∀ j : Fin 3, ContDiffOn ℝ ∞ (C0 j) U) ∧
    ContDiffOn ℝ ∞ D0 U ∧
    ∀ radiusPower : ℕ, 1 ≤ radiusPower → radiusPower ≤ 3 →
      HasCoordinateWordJetBound 3
        (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) x
        (Cscaled*eta^radiusPower/beta^(2*radiusPower)) beta 0 ∧
      ∀ i j : Fin 3, HasCoordinateWordJetBound 3
        (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) x
        (Cscaled*eta^radiusPower/beta^(2*radiusPower)) beta 0 := by
  intro Ω SegΩ V χ U S N C0 D0 hxU hRaw
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.prodMk (contDiff_id.prodMk hR)
  have hχ0 : ContDiff ℝ ∞ (fun y : R3 => (q,(y,(0 : ℝ)))) :=
    contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hOpen := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hU : IsOpen U := hOpen.1
  have hSOn (radiusPower : ℕ) : ContDiffOn ℝ ∞
      (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) U := by
    intro y hy
    have hS := ContDiffAt.fun_comp (f := χ) (g := S) y
      ((contDiffAt_referencePairedRadialSecondRemainder_low_input_families_of_segment
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y (R y) hy.2.1).1)
      hχ.contDiffAt
    exact ((hR.contDiffAt.pow radiusPower).smul hS).contDiffWithinAt
  have hNOn (radiusPower : ℕ) (i j : Fin 3) : ContDiffOn ℝ ∞
      (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) U := by
    intro y hy
    have hN := ContDiffAt.fun_comp (f := χ) (g := N i j) y
      (contDiffAt_nativeNegativeHalf_referenceJacobiBoundaryCoefficientFamily
        g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (χ y) hy.2.2)
      hχ.contDiffAt
    exact ((hR.contDiffAt.pow radiusPower).smul hN).contDiffWithinAt
  have hC0On (j : Fin 3) : ContDiffOn ℝ ∞ (C0 j) U := by
    intro y hy
    have h0 : (q,(y,0)) ∈ Ω := by
      simpa only [zero_mul] using hy.2.1 0 ⟨le_rfl,zero_le_one⟩
    have hzFields := h0
    unfold Ω referenceRadialEndpointInvertibleLocus at hzFields
    have hC := contDiffAt_referenceLowerCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j hzFields.2.2 hzFields.2.1
    exact (ContDiffAt.fun_comp (f := fun y : R3 => (q,(y,(0 : ℝ))))
      (g := fun z : ℝ × (R3 × ℝ) => referenceLowerCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j) y hC hχ0.contDiffAt).contDiffWithinAt
  let Dj : (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun z =>
    deriv (fun t : ℝ => referenceLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
  have hDj : ContDiffOn ℝ ∞ Dj Ω :=
    contDiffOn_deriv_joint_radialSlice
      (referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) Ω hΩ
      (contDiffOn_referenceLowerRadialEndpointFamily_invertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
  have hD0On : ContDiffOn ℝ ∞ D0 U := by
    intro y hy
    have h0 : (q,(y,0)) ∈ Ω := by
      simpa only [zero_mul] using hy.2.1 0 ⟨le_rfl,zero_le_one⟩
    change ContDiffWithinAt ℝ ∞ (fun y : R3 => Dj (q,(y,0))) U y
    exact (ContDiffAt.fun_comp (f := fun y : R3 => (q,(y,(0 : ℝ))))
      (g := Dj) y (hDj.contDiffAt (hΩ.mem_nhds h0)) hχ0.contDiffAt).contDiffWithinAt
  have hSBound (radiusPower : ℕ) (ha1 : 1 ≤ radiusPower) (ha3 : radiusPower ≤ 3) :
      HasCoordinateWordJetBound 3
        (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) x
        (Cscaled*eta^radiusPower/beta^(2*radiusPower)) beta 0 := by
    intro word hw
    have hActual := hRaw radiusPower ha1 ha3 word.length hw
    have hJet : ‖iteratedFDeriv ℝ word.length
        (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) x‖ ≤
          Cscaled*eta^radiusPower*beta^word.length/beta^(2*radiusPower) := by
      simpa only [one_mul] using hActual.1
    calc
      _ ≤ ‖iteratedFDeriv ℝ word.length
          (fun y : R3 => (R y)^radiusPower • S (q,(y,R y))) x‖ :=
        norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen word _ U hU (hSOn radiusPower) x hxU
      _ ≤ Cscaled*eta^radiusPower*beta^word.length/beta^(2*radiusPower) := hJet
      _ = (Cscaled*eta^radiusPower/beta^(2*radiusPower))*beta^(0+word.length) := by
        simp only [Nat.zero_add]; ring
  have hNBound (radiusPower : ℕ) (ha1 : 1 ≤ radiusPower) (ha3 : radiusPower ≤ 3) (i j : Fin 3) :
      HasCoordinateWordJetBound 3
        (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) x
        (Cscaled*eta^radiusPower/beta^(2*radiusPower)) beta 0 := by
    intro word hw
    have hActual := hRaw radiusPower ha1 ha3 word.length hw
    have hJet : ‖iteratedFDeriv ℝ word.length
        (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) x‖ ≤
          Cscaled*eta^radiusPower*beta^word.length/beta^(2*radiusPower) := by
      simpa only [one_mul] using hActual.2 i j
    calc
      _ ≤ ‖iteratedFDeriv ℝ word.length
          (fun y : R3 => (R y)^radiusPower • N i j (q,(y,R y))) x‖ :=
        norm_coordinateFieldWordPartial_le_iteratedFDeriv_of_isOpen word _ U hU (hNOn radiusPower i j) x hxU
      _ ≤ Cscaled*eta^radiusPower*beta^word.length/beta^(2*radiusPower) := hJet
      _ = (Cscaled*eta^radiusPower/beta^(2*radiusPower))*beta^(0+word.length) := by
        simp only [Nat.zero_add]; ring
  exact ⟨hSOn,hNOn,hC0On,hD0On,fun a ha1 ha3 =>
    ⟨hSBound a ha1 ha3,fun i j => hNBound a ha1 ha3 i j⟩⟩

lemma norm_referenceAdjointMovingDifferenceQuotientPivotHigh_profile_coordinate_wordPartial_le
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (x : R3) (Cscaled eta beta Bstatic Flog m : ℝ)
    (hCscaled : 0 ≤ Cscaled) (hBstatic : 0 ≤ Bstatic) (hFlog : 0 ≤ Flog)
    (hbeta : 1 ≤ beta) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) :
    let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let SegΩ : Set (ℝ × (R3 × ℝ)) :=
      {z | ∀ θ ∈ Icc (0 : ℝ) 1, (z.1,(z.2.1,θ*z.2.2)) ∈ Ω}
    let V : Set (ℝ × (R3 × ℝ)) := {z | ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible}
    let χ : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
    let U : Set R3 := {y | R y ≠ 0 ∧ χ y ∈ SegΩ ∧ χ y ∈ V}
    let S : (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun z =>
      referenceSharpRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let N : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → Half →L[ℝ] Half := fun i j z =>
      nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j z)
    let C0 : Fin 3 → R3 → Hi →L[ℝ] Half := fun j y =>
      referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let D0 : R3 → Hi →L[ℝ] Half := fun y =>
      deriv (fun t : ℝ => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    let M : Fin 3 → Half →L[ℝ] Half := fun j =>
      sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
    let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
    x ∈ U →
    (∀ radiusPower : ℕ, 1 ≤ radiusPower → radiusPower ≤ 3 →
      ∀ order : ℕ, order ≤ 3 →
        ‖iteratedFDeriv ℝ order (fun y : R3 => ((1 : ℝ)*R y)^radiusPower •
          S (q,(y,(1 : ℝ)*R y))) x‖ ≤ Cscaled*eta^radiusPower*beta^order/beta^(2*radiusPower) ∧
        ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ order (fun y : R3 => ((1 : ℝ)*R y)^radiusPower •
          N i j (q,(y,(1 : ℝ)*R y))) x‖ ≤ Cscaled*eta^radiusPower*beta^order/beta^(2*radiusPower)) →
    (∀ j : Fin 3, HasCoordinateWordJetBound 3 (C0 j) x Bstatic beta 0) →
    HasCoordinateWordJetBound 3 D0 x Bstatic beta 0 →
    (∀ i : Fin 3, HasCoordinateWordJetBound 3 (f i) x Flog beta 1) →
    (∀ j : Fin 3, ‖M j‖ ≤ m) →
    ∀ power : ℕ, 1 ≤ power → power ≤ 2 → ∀ i : Fin 3,
      ∀ word : List (Fin 3), word.length ≤ 3 →
      ‖coordinateFieldWordPartial word
        (fun y : R3 => (R y)^power • referenceAdjointMovingDifferenceQuotientPivotHigh
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) x‖ ≤
        (Cscaled*m+24*Bstatic*Cscaled+24*Bstatic*m*Cscaled+24*Cscaled^2*m+8*Flog*Cscaled)*
          eta^power*beta^word.length/beta^(2*power) := by
  intro Ω SegΩ V χ U S N C0 D0 M f hxU hRaw hC0B hD0B hfB hM
  have hEndpointData := referencePairedRadialJacobi_profile_high_coordinate_word_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR x Cscaled eta beta hxU hRaw
  rcases hEndpointData with ⟨hSOn,hNOn,hC0On,hD0On,hCaps⟩
  have hOpen := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hU : IsOpen U := hOpen.1
  have hfOn (i : Fin 3) : ContDiffOn ℝ ∞ (f i) U := hOpen.2.2.2.2.2.1 i
  let Sprof : R3 → Hi →L[ℝ] Half := fun y => S (q,(y,R y))
  let Nprof : Fin 3 → Fin 3 → R3 → Half →L[ℝ] Half := fun i j y => N i j (q,(y,R y))
  letI : DistribMulAction ℝ (Hi →L[ℝ] Half) :=
    ContinuousLinearMap.distribMulAction (R := ℝ) (R₂ := ℝ) (S₃ := ℝ)
      (M := Hi) (M₂ := Half) (σ₁₂ := RingHom.id ℝ)
  letI : DistribSMul ℝ (Hi →L[ℝ] Half) := DistribMulAction.toDistribSMul
  intro power hpower1 hpower2 i word hw
  have hpower3 : power ≤ 3 := by omega
  have hnext1 : 1 ≤ power+1 := by omega
  have hnext3 : power+1 ≤ 3 := by omega
  let Ext : R3 → Hi →L[ℝ] Half := fun y =>
    (M i).comp ((R y)^power • Sprof y) +
    (∑ j : Fin 3, ((R y)^power • Nprof i j y).comp (C0 j y)) +
    (∑ j : Fin 3, ((R y)^(power+1) • Nprof i j y).comp ((M j).comp (D0 y))) +
    (∑ j : Fin 3, ((R y)^2 • Nprof i j y).comp ((M j).comp ((R y)^power • Sprof y))) +
    f i y • ((R y)^(power+1) • Sprof y)
  have hEstimate := norm_coordinateFieldWordPartial_reversed_clm_sum_le (E := Hi) (V := Half) power
    (fun y => (R y)^power • Sprof y) (fun y => (R y)^(power+1) • Sprof y)
    D0 C0
    (fun j y => (R y)^power • Nprof i j y) (fun j y => (R y)^(power+1) • Nprof i j y)
    (fun j y => (R y)^2 • Nprof i j y) M (f i) i U hU
    (hSOn power) (hSOn (power+1)) hD0On hC0On
    (fun j => hNOn power i j) (fun j => hNOn (power+1) i j) (fun j => hNOn 2 i j)
    (hfOn i) x hxU Cscaled Bstatic Flog m beta eta hCscaled hBstatic hFlog hM
    hbeta heta heta1 (hCaps power hpower1 hpower3).1 (hCaps (power+1) hnext1 hnext3).1
    hD0B hC0B
    (fun j => (hCaps power hpower1 hpower3).2 i j)
    (fun j => (hCaps (power+1) hnext1 hnext3).2 i j)
    (fun j => (hCaps 2 (by norm_num) (by norm_num)).2 i j) (hfB i) word hw
  have hFunctions : (fun y : R3 => (R y)^power • referenceAdjointMovingDifferenceQuotientPivotHigh
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) = Ext := by
    funext y
    have hNext : (R y)^power*R y = (R y)^(power+1) := (pow_succ (R y) power).symm
    have hLast : (R y)^power*(R y*referenceRadiusHorizontalLogDerivative g L q R y i) =
        referenceRadiusHorizontalLogDerivative g L q R y i*(R y)^(power+1) := by rw [pow_succ]; ring
    have hSquare : (R y)^power*(R y)^2 = (R y)^2*(R y)^power := mul_comm _ _
    simp only [referenceAdjointMovingDifferenceQuotientPivotHigh,Ext,Sprof,Nprof,S,N,C0,D0,M,f,χ,
      ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_add,Finset.smul_sum,
      smul_smul,hNext,hLast,hSquare]
  have hWord := congrArg (fun F : R3 → Hi →L[ℝ] Half => coordinateFieldWordPartial word F x) hFunctions
  have hNorm := congrArg norm hWord
  exact hNorm.trans_le hEstimate

lemma norm_referenceAdjointMovingDifferenceQuotientPivotLow_profile_coordinate_wordPartial_le
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1)
    (R : R3 → ℝ) (hR : ContDiff ℝ ∞ R)
    (x : R3) (Cscaled eta beta Bstatic Flog m : ℝ)
    (hCscaled : 0 ≤ Cscaled) (hBstatic : 0 ≤ Bstatic) (hFlog : 0 ≤ Flog)
    (hbeta : 1 ≤ beta) (heta : 0 ≤ eta) (heta1 : eta ≤ 1) :
    let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let SegΩ : Set (ℝ × (R3 × ℝ)) :=
      {z | ∀ θ ∈ Icc (0 : ℝ) 1, (z.1,(z.2.1,θ*z.2.2)) ∈ Ω}
    let V : Set (ℝ × (R3 × ℝ)) := {z | ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible}
    let χ : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
    let U : Set R3 := {y | R y ≠ 0 ∧ χ y ∈ SegΩ ∧ χ y ∈ V}
    let S : (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun z =>
      referenceLowerRadialTraceSecondRemainder g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z.1 z.2.1 z.2.2
    let N : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) → Neg →L[ℝ] Neg := fun i j z =>
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData i j z)
    let C0 : Fin 3 → R3 → Half →L[ℝ] Neg := fun j y =>
      referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,0)) j
    let D0 : R3 → Half →L[ℝ] Neg := fun y =>
      deriv (fun t : ℝ => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) 0
    let M : Fin 3 → Neg →L[ℝ] Neg := fun j =>
      sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
    let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
    x ∈ U →
    (∀ radiusPower : ℕ, 1 ≤ radiusPower → radiusPower ≤ 3 →
      ∀ order : ℕ, order ≤ 3 →
        ‖iteratedFDeriv ℝ order (fun y : R3 => ((1 : ℝ)*R y)^radiusPower •
          S (q,(y,(1 : ℝ)*R y))) x‖ ≤ Cscaled*eta^radiusPower*beta^order/beta^(2*radiusPower) ∧
        ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ order (fun y : R3 => ((1 : ℝ)*R y)^radiusPower •
          N i j (q,(y,(1 : ℝ)*R y))) x‖ ≤ Cscaled*eta^radiusPower*beta^order/beta^(2*radiusPower)) →
    (∀ j : Fin 3, HasCoordinateWordJetBound 3 (C0 j) x Bstatic beta 0) →
    HasCoordinateWordJetBound 3 D0 x Bstatic beta 0 →
    (∀ i : Fin 3, HasCoordinateWordJetBound 3 (f i) x Flog beta 1) →
    (∀ j : Fin 3, ‖M j‖ ≤ m) →
    ∀ power : ℕ, 1 ≤ power → power ≤ 2 → ∀ i : Fin 3,
      ∀ word : List (Fin 3), word.length ≤ 3 →
      ‖coordinateFieldWordPartial word
        (fun y : R3 => (R y)^power • referenceAdjointMovingDifferenceQuotientPivotLow
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) x‖ ≤
        (Cscaled*m+24*Bstatic*Cscaled+24*Bstatic*m*Cscaled+24*Cscaled^2*m+8*Flog*Cscaled)*
          eta^power*beta^word.length/beta^(2*power) := by
  intro Ω SegΩ V χ U S N C0 D0 M f hxU hRaw hC0B hD0B hfB hM
  have hEndpointData := referencePairedRadialJacobi_profile_low_coordinate_word_data
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR x Cscaled eta beta hxU hRaw
  rcases hEndpointData with ⟨hSOn,hNOn,hC0On,hD0On,hCaps⟩
  have hOpen := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hU : IsOpen U := hOpen.1
  have hfOn (i : Fin 3) : ContDiffOn ℝ ∞ (f i) U := hOpen.2.2.2.2.2.1 i
  let Sprof : R3 → Half →L[ℝ] Neg := fun y => S (q,(y,R y))
  let Nprof : Fin 3 → Fin 3 → R3 → Neg →L[ℝ] Neg := fun i j y => N i j (q,(y,R y))
  letI : DistribMulAction ℝ (Half →L[ℝ] Neg) :=
    ContinuousLinearMap.distribMulAction (R := ℝ) (R₂ := ℝ) (S₃ := ℝ)
      (M := Half) (M₂ := Neg) (σ₁₂ := RingHom.id ℝ)
  letI : DistribSMul ℝ (Half →L[ℝ] Neg) := DistribMulAction.toDistribSMul
  intro power hpower1 hpower2 i word hw
  have hpower3 : power ≤ 3 := by omega
  have hnext1 : 1 ≤ power+1 := by omega
  have hnext3 : power+1 ≤ 3 := by omega
  let Ext : R3 → Half →L[ℝ] Neg := fun y =>
    (M i).comp ((R y)^power • Sprof y) +
    (∑ j : Fin 3, ((R y)^power • Nprof i j y).comp (C0 j y)) +
    (∑ j : Fin 3, ((R y)^(power+1) • Nprof i j y).comp ((M j).comp (D0 y))) +
    (∑ j : Fin 3, ((R y)^2 • Nprof i j y).comp ((M j).comp ((R y)^power • Sprof y))) +
    f i y • ((R y)^(power+1) • Sprof y)
  have hEstimate := norm_coordinateFieldWordPartial_reversed_clm_sum_le (E := Half) (V := Neg) power
    (fun y => (R y)^power • Sprof y) (fun y => (R y)^(power+1) • Sprof y)
    D0 C0
    (fun j y => (R y)^power • Nprof i j y) (fun j y => (R y)^(power+1) • Nprof i j y)
    (fun j y => (R y)^2 • Nprof i j y) M (f i) i U hU
    (hSOn power) (hSOn (power+1)) hD0On hC0On
    (fun j => hNOn power i j) (fun j => hNOn (power+1) i j) (fun j => hNOn 2 i j)
    (hfOn i) x hxU Cscaled Bstatic Flog m beta eta hCscaled hBstatic hFlog hM
    hbeta heta heta1 (hCaps power hpower1 hpower3).1 (hCaps (power+1) hnext1 hnext3).1
    hD0B hC0B
    (fun j => (hCaps power hpower1 hpower3).2 i j)
    (fun j => (hCaps (power+1) hnext1 hnext3).2 i j)
    (fun j => (hCaps 2 (by norm_num) (by norm_num)).2 i j) (hfB i) word hw
  have hFunctions : (fun y : R3 => (R y)^power • referenceAdjointMovingDifferenceQuotientPivotLow
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) = Ext := by
    funext y
    have hNext : (R y)^power*R y = (R y)^(power+1) := (pow_succ (R y) power).symm
    have hLast : (R y)^power*(R y*referenceRadiusHorizontalLogDerivative g L q R y i) =
        referenceRadiusHorizontalLogDerivative g L q R y i*(R y)^(power+1) := by rw [pow_succ]; ring
    have hSquare : (R y)^power*(R y)^2 = (R y)^2*(R y)^power := mul_comm _ _
    simp only [referenceAdjointMovingDifferenceQuotientPivotLow,Ext,Sprof,Nprof,S,N,C0,D0,M,f,χ,
      ContinuousLinearMap.smul_comp,ContinuousLinearMap.comp_smul,smul_add,Finset.smul_sum,
      smul_smul,hNext,hLast,hSquare]
  have hWord := congrArg (fun F : R3 → Half →L[ℝ] Neg => coordinateFieldWordPartial word F x) hFunctions
  have hNorm := congrArg norm hWord
  exact hNorm.trans_le hEstimate

theorem exists_referenceAdjointMovingDifferenceQuotientPivot_profile_radiusPower_coordinate_word_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) (hKgeom : K ⊆ closedBall y0 ρ) :
    ∃ dGeom Cbar : ℝ, 0 < dGeom ∧ dGeom ≤ ρ ∧ dGeom ≤ 1 ∧
      ((Set.prod (Icc (0 : ℝ) 1) (Set.prod (closedBall y0 ρ) (Icc (-dGeom) dGeom))) ⊆
        referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) ∧
      0 < Cbar ∧ ∃ p0 : ℕ, 2 ≤ p0 ∧
      ∀ p : ℕ, p0 ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
      ∃ A : ℝ, 0 < A ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ x ∈ K,
        let beta : ℝ := actualReferenceBeta g L q delta A p x
        referenceRadius delta A p L x ≤ dGeom ∧ 1 ≤ beta ∧
        referenceRadius delta A p L x * beta^2 ≤ eta ∧
        ∀ power : ℕ, 1 ≤ power → power ≤ 2 →
        ∀ i : Fin 3, ∀ word : List (Fin 3), word.length ≤ 3 →
          ‖coordinateFieldWordPartial word
            (fun y : R3 => (referenceRadius delta A p L y)^power •
              referenceAdjointMovingDifferenceQuotientPivotHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q
                (referenceRadius delta A p L) y i) x‖ ≤
            Cbar * eta^power * beta^word.length / beta^(2*power) ∧
          ‖coordinateFieldWordPartial word
            (fun y : R3 => (referenceRadius delta A p L y)^power •
              referenceAdjointMovingDifferenceQuotientPivotLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q
                (referenceRadius delta A p L) y i) x‖ ≤
            Cbar * eta^power * beta^word.length / beta^(2*power) := by
  classical
  let Ω := referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hΩ : IsOpen Ω := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hProfile := exists_referencePairedRadialJacobi_profile_scaled_jets
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hg hL K hK hKgeom
  rcases hProfile with ⟨dGeom,Cscaled,hdGeom,hdGeomρ,hdGeom1,hRoom,hCscaled,p0,hp02,hProfiles⟩
  have hStatic := exists_referenceBoundary_static_zero_radial_coordinate_word_bounds
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 dGeom hdGeom hRoom
  rcases hStatic with ⟨Bh,Bl,hBh,hBl,hStaticCaps⟩
  let Ch : Fin 3 → (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun j z => referenceHighCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j
  let Dh : (ℝ × (R3 × ℝ)) → Hi →L[ℝ] Half := fun z =>
    deriv (fun t : ℝ => referenceSharpRadialTraceFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
  let Cl : Fin 3 → (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun j z => referenceLowerCoordinateBoundaryFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z j
  let Dl : (ℝ × (R3 × ℝ)) → Half →L[ℝ] Neg := fun z =>
    deriv (fun t : ℝ => referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
  have hLog := exists_referenceDD_logRadius_frame_uniform_coordinate_word_bounds g hg L hL K hK 3
  rcases hLog with ⟨Flog,hFlog,hLogBounds⟩
  let Mh : Fin 3 → Half →L[ℝ] Half := fun j => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
  let Ml : Fin 3 → Neg →L[ℝ] Neg := fun j => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
  let mh : ℝ := 1+∑ j : Fin 3, ‖Mh j‖
  let ml : ℝ := 1+∑ j : Fin 3, ‖Ml j‖
  have hmh0 : 0 ≤ mh := add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ => norm_nonneg (Mh j)))
  have hml0 : 0 ≤ ml := add_nonneg zero_le_one (Finset.sum_nonneg (fun j _ => norm_nonneg (Ml j)))
  have hMh (j : Fin 3) : ‖Mh j‖ ≤ mh := by
    have h := Finset.single_le_sum (fun k _ => norm_nonneg (Mh k)) (Finset.mem_univ j)
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  have hMl (j : Fin 3) : ‖Ml j‖ ≤ ml := by
    have h := Finset.single_le_sum (fun k _ => norm_nonneg (Ml k)) (Finset.mem_univ j)
    exact h.trans (le_add_of_nonneg_left zero_le_one)
  have hC0 : 0 ≤ Cscaled := zero_le_one.trans hCscaled
  let Kh : ℝ := Cscaled*mh+24*Bh*Cscaled+24*Bh*mh*Cscaled+24*Cscaled^2*mh+8*Flog*Cscaled
  let Kl : ℝ := Cscaled*ml+24*Bl*Cscaled+24*Bl*ml*Cscaled+24*Cscaled^2*ml+8*Flog*Cscaled
  let Cbar : ℝ := 1+Kh+Kl
  have hKh : 0 ≤ Kh := by dsimp only [Kh]; positivity
  have hKl : 0 ≤ Kl := by dsimp only [Kl]; positivity
  have hCbar : 0 < Cbar := by dsimp only [Cbar]; positivity
  have hKhCbar : Kh ≤ Cbar := by dsimp only [Cbar]; linarith only [hKl]
  have hKlCbar : Kl ≤ Cbar := by dsimp only [Cbar]; linarith only [hKh]
  refine ⟨dGeom,Cbar,hdGeom,hdGeomρ,hdGeom1,hRoom,hCbar,p0,hp02,?_⟩
  intro p hp eta heta heta1
  have hAmplitude := hProfiles p hp eta heta heta1
  rcases hAmplitude with ⟨A,hA,hAll⟩
  refine ⟨A,hA,?_⟩
  intro q hq delta hdelta hdelta1 x hx beta
  have hPoint := hAll q hq delta hdelta hdelta1 x hx
  refine ⟨hPoint.1,hPoint.2.1,hPoint.2.2.1,?_⟩
  have hp1 : 1 ≤ p := by omega
  let R : R3 → ℝ := referenceRadius delta A p L
  have hRpos (y : R3) : 0 < R y := referenceRadius_pos delta A p L y hdelta hA
  have hLogR : ContDiff ℝ ∞ (fun y => Real.log (R y)) := contDiff_log_referenceRadius_profile delta A L p hdelta hA
  have hR : ContDiff ℝ ∞ R := by
    have hExp : (fun y => Real.exp (Real.log (R y))) = R := funext (fun y => Real.exp_log (hRpos y))
    exact hExp ▸ Real.contDiff_exp.comp hLogR
  let SegΩ : Set (ℝ × (R3 × ℝ)) := {z | ∀ θ ∈ Icc (0 : ℝ) 1, (z.1,(z.2.1,θ*z.2.2)) ∈ Ω}
  let V : Set (ℝ × (R3 × ℝ)) := {z | ∀ ξ : UnitSphere,
    (referenceFramedNormalizedJacobian g L Φ (z.1,(z.2,ξ.val))).IsInvertible}
  let χ : R3 → ℝ × (R3 × ℝ) := fun y => (q,(y,R y))
  let U : Set R3 := {y | R y ≠ 0 ∧ χ y ∈ SegΩ ∧ χ y ∈ V}
  have hχ : ContDiff ℝ ∞ χ := contDiff_const.prodMk (contDiff_id.prodMk hR)
  have hχ0 : ContDiff ℝ ∞ (fun y : R3 => (q,(y,(0 : ℝ)))) := contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hxBall : x ∈ closedBall y0 ρ := hKgeom hx
  have hxSegment : χ x ∈ SegΩ := by
    intro θ hθ
    have hθr : |θ*R x| ≤ dGeom := by
      rw [abs_mul,abs_of_nonneg hθ.1,abs_of_pos (hRpos x)]
      exact (mul_le_mul_of_nonneg_right hθ.2 (hRpos x).le).trans (by simpa only [one_mul] using hPoint.1)
    exact hRoom ⟨hq,hxBall,abs_le.mp hθr⟩
  have hCover := referenceFramedNormalizedJacobian_isInvertible_on_actual_coefficient_tube
    g L y0 Φ B ε C ρ H a w hData dGeom hdGeom hdGeomρ
  have hxInv : χ x ∈ V := hCover (χ x) ⟨hq,hxBall,
    ⟨(neg_nonpos.mpr hdGeom.le).trans (hRpos x).le,hPoint.1⟩⟩
  have hxU : x ∈ U := ⟨(hRpos x).ne',hxSegment,hxInv⟩
  have hOpen := contDiffOn_referenceHighAdjoint_weighted_correction_open_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR
  have hU : IsOpen U := hOpen.1
  let f : Fin 3 → R3 → ℝ := fun i y => referenceRadiusHorizontalLogDerivative g L q R y i
  have hfEq (i : Fin 3) : f i = AmbientReferenceRaising.referenceFrameDerivative g L q i (fun y => Real.log (R y)) := by
    funext y
    have hFrame : conformalReferenceGramFrameOperatorJoint g L (q,y) (coordinateVector i) = referenceMetricGramFrame g L (q,y) i :=
      (congrArg (fun A : R3 →L[ℝ] R3 => A (coordinateVector i))
        (conformalReferenceGramFrameOperatorJoint_eq_frameOperator g L (q,y))).trans
        ((frameOperator_coordinateVector _ i).trans (conformalReferenceGramFrame_eq_referenceMetricGramFrame g L q y i))
    unfold f referenceRadiusHorizontalLogDerivative AmbientReferenceRaising.referenceFrameDerivative
    exact congrArg (fderiv ℝ (fun y => Real.log (R y)) y) hFrame
  have hfBound (i : Fin 3) : HasCoordinateWordJetBound 3 (f i) x Flog beta 1 := by
    intro word hw
    rw [hfEq]
    have h := (hLogBounds q hq delta hdelta hdelta1 A hA p hp1 x hx hPoint.2.1 word hw).1 i
    simpa only [Real.norm_eq_abs,R,beta,actualReferenceBeta] using h
  have hfOn (i : Fin 3) : ContDiffOn ℝ ∞ (f i) U := hOpen.2.2.2.2.2.1 i
  have hRawHigh := fun (a : ℕ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (n : ℕ) (hn : n ≤ 3) =>
    let h := hPoint.2.2.2 (1 : ℝ) (by norm_num) a ha1 ha3 n hn
    And.intro h.1 (fun (i j : Fin 3) => (h.2.2.2.2 i j).2.1)
  have hRawLow := fun (a : ℕ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (n : ℕ) (hn : n ≤ 3) =>
    let h := hPoint.2.2.2 (1 : ℝ) (by norm_num) a ha1 ha3 n hn
    And.intro h.2.1 (fun (i j : Fin 3) => (h.2.2.2.2 i j).2.2)
  have hHighEstimate := norm_referenceAdjointMovingDifferenceQuotientPivotHigh_profile_coordinate_wordPartial_le
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR x
    Cscaled eta beta Bh Flog mh hC0 hBh hFlog.le hPoint.2.1 heta.le heta1
    hxU hRawHigh
    (fun j => (hStaticCaps q hq x hxBall beta hPoint.2.1 j).1)
    (hStaticCaps q hq x hxBall beta hPoint.2.1 (0 : Fin 3)).2.1
    hfBound hMh
  have hLowEstimate := norm_referenceAdjointMovingDifferenceQuotientPivotLow_profile_coordinate_wordPartial_le
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg q hq R hR x
    Cscaled eta beta Bl Flog ml hC0 hBl hFlog.le hPoint.2.1 heta.le heta1
    hxU hRawLow
    (fun j => (hStaticCaps q hq x hxBall beta hPoint.2.1 j).2.2.1)
    (hStaticCaps q hq x hxBall beta hPoint.2.1 (0 : Fin 3)).2.2.2
    hfBound hMl
  intro power hpower1 hpower2 i word hw
  have hScale : 0 ≤ eta^power*beta^word.length/beta^(2*power) :=
    div_nonneg (mul_nonneg (pow_nonneg heta.le _) (pow_nonneg (zero_le_one.trans hPoint.2.1) _))
      (pow_nonneg (zero_le_one.trans hPoint.2.1) _)
  constructor
  · have hEstimate := hHighEstimate power hpower1 hpower2 i word hw
    have hBound : ‖coordinateFieldWordPartial word
        (fun y : R3 => (R y)^power • referenceAdjointMovingDifferenceQuotientPivotHigh
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) x‖ ≤
        Kh*eta^power*beta^word.length/beta^(2*power) := hEstimate
    exact hBound.trans (by
      calc
        Kh*eta^power*beta^word.length/beta^(2*power) = Kh*(eta^power*beta^word.length/beta^(2*power)) := by ring
        _ ≤ Cbar*(eta^power*beta^word.length/beta^(2*power)) := mul_le_mul_of_nonneg_right hKhCbar hScale
        _ = Cbar*eta^power*beta^word.length/beta^(2*power) := by ring)
  · have hEstimate := hLowEstimate power hpower1 hpower2 i word hw
    have hBound : ‖coordinateFieldWordPartial word
        (fun y : R3 => (R y)^power • referenceAdjointMovingDifferenceQuotientPivotLow
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R y i) x‖ ≤
        Kl*eta^power*beta^word.length/beta^(2*power) := hEstimate
    exact hBound.trans (by
      calc
        Kl*eta^power*beta^word.length/beta^(2*power) = Kl*(eta^power*beta^word.length/beta^(2*power)) := by ring
        _ ≤ Cbar*(eta^power*beta^word.length/beta^(2*power)) := mul_le_mul_of_nonneg_right hKlCbar hScale
        _ = Cbar*eta^power*beta^word.length/beta^(2*power) := by ring)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMovingDifferenceQuotientPivotHigh
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMovingDifferenceQuotientPivotLow
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMovingDifferenceQuotientPivot_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.sphereSobolevDualPairing_referenceAdjointMovingDifferenceQuotientPivot
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffOn_referenceAdjointMovingDifferenceQuotientPivot
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceAdjointMovingDifferenceQuotientPivot_profile_radiusPower_coordinate_word_bounds
