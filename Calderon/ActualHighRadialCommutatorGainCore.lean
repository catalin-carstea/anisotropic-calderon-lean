import Calderon.ActualReferenceRadialAdjointSharpSecondCommutatorCoercivity
import Calderon.ActualReferenceSharpRotationRemainderDefinition
import Calderon.ActualHighSmoothMultiplierBoundaryCommutator
import Calderon.ActualHighSmoothMultiplierFixedTopology
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.SignedTaylorFixedLinearTransport

/-! High radial commutator gain. The only local instances are the Prop-valued
`CompleteSpace` facts for the existing lp carriers. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Topology

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
  NativeThreeHalfCoefficientMultiplier NativeOrderOneCoefficientMultiplier
attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceSharpRadialTraceFamily
  referenceAdjointThreeHalfRadialFamily referenceAdjointHalfRadialFamily
  referenceSharpRadialTraceSecondRemainder referenceLowerRadialTraceSecondRemainder
  secondTaylorRemainder sphereSobolevInclusionL nativeThreeHalfCoefficientMulL
  nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL realHalfOperatorAdjointL
  referenceGaugeNormalHighInvertibleLocus
  referenceStrongDriftFamily referenceWeakDirichletEnergyFamily
  referenceNormalizedAdjointHighDefectFamily referenceNormalizedAdjointHalfDefectFamily
  referenceRadialSkewProductJets referenceRadialSkewDerivativeJets
  referenceRadialTangentSecondCommutator referenceRadialDefectSecondCommutator
  referenceRadialAdjointSharpSecondCommutator referenceSharpRadialRotationSecondRemainder
  referenceLowerRadialRotationSecondRemainder referenceSharpRadialRotationCommutatorL
  referenceLowerRadialRotationCommutatorL sphereSobolevRotationL harmonicSphereSubspace
open SmoothSphereRotation NativeH2ThreeHalfValueTrace NativeHarmonicLiftCompletion

/-! ### H1. Four-carrier signed-Taylor transport, proved constructively from
`secondTaylorRemainder_fixed_linear_map` and
`secondTaylorRemainder_eq_of_locallyEq_on_segment` (the three-carrier
`secondTaylorRemainder_operator_intertwining` forces `I`'s codomain to be `F`'s). -/

lemma secondTaylorRemainder_endpoint_intertwining
    {X X' Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup X'] [NormedSpace ℝ X']
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (F : ℝ → X →L[ℝ] Y) (A : ℝ → X' →L[ℝ] Z)
    (I : X →L[ℝ] X') (J : Y →L[ℝ] Z) (r : ℝ)
    (hF : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (θ*r))
    (hA : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ A (θ*r))
    (hEq : ∀ θ ∈ Icc (0 : ℝ) 1,
      (fun z => J.comp (F z)) =ᶠ[𝓝 (θ*r)] (fun z => (A z).comp I)) :
    J.comp (secondTaylorRemainder F r) = (secondTaylorRemainder A r).comp I := by
  let postLinear : (X →L[ℝ] Y) →ₗ[ℝ] (X →L[ℝ] Z) :=
    { toFun := fun T => J.comp T
      map_add' := fun T U => by
        apply ContinuousLinearMap.ext
        intro x
        exact J.map_add (T x) (U x)
      map_smul' := fun c T => by
        apply ContinuousLinearMap.ext
        intro x
        exact J.map_smul c (T x) }
  let Post : (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] Z) :=
    LinearMap.mkContinuous postLinear ‖J‖ (fun T => J.opNorm_comp_le T)
  let preLinear : (X' →L[ℝ] Z) →ₗ[ℝ] (X →L[ℝ] Z) :=
    { toFun := fun T => T.comp I
      map_add' := fun T U => rfl
      map_smul' := fun c T => rfl }
  have hPreBound (T : X' →L[ℝ] Z) : ‖preLinear T‖ ≤ ‖I‖*‖T‖ :=
    (T.opNorm_comp_le I).trans_eq (mul_comm _ _)
  let Pre : (X' →L[ℝ] Z) →L[ℝ] (X →L[ℝ] Z) :=
    LinearMap.mkContinuous preLinear ‖I‖ hPreBound
  have hPostApply (T : X →L[ℝ] Y) : Post T = J.comp T := rfl
  have hPreApply (T : X' →L[ℝ] Z) : Pre T = T.comp I := rfl
  have hSame (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun z => Post (F z)) =ᶠ[𝓝 (θ*r)] (fun z => Pre (A z)) := by
    filter_upwards [hEq θ hθ] with z hz
    exact (hPostApply _).trans (hz.trans (hPreApply _).symm)
  have hFmap : Post (secondTaylorRemainder F r) =
      secondTaylorRemainder (fun z => Post (F z)) r :=
    secondTaylorRemainder_fixed_linear_map F Post r hF
  have hAmap : Pre (secondTaylorRemainder A r) =
      secondTaylorRemainder (fun z => Pre (A z)) r :=
    secondTaylorRemainder_fixed_linear_map A Pre r hA
  have hMiddle : secondTaylorRemainder (fun z => Post (F z)) r =
      secondTaylorRemainder (fun z => Pre (A z)) r :=
    secondTaylorRemainder_eq_of_locallyEq_on_segment _ _ r hSame
  exact (hPostApply _).symm.trans
    (hFmap.trans (hMiddle.trans (hAmap.symm.trans (hPreApply _))))

/-! ### H8. Adjacent gained commutator: high realization, abstract endpoint algebra.
`CHigh = -KH MHi MHk - Sh GAi MHk - Gi Th MHk + Th GHi MHk + Th MHi GHk` realizes the
lower form `-MNi Kl MLk + MNi Tl Gk - Gni MNk Sl` (MINUS kept). Every
hypothesis is an existing actual graph. -/

theorem adjacentGainedCommutator_high_lower_graph
    {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z)
    (KH Th Sh : X →L[ℝ] Y) (Kl Tl Sl : Y →L[ℝ] Z)
    (MHi MHk GHi GHk GAi : X →L[ℝ] X) (MLi MLk Gi Gk : Y →L[ℝ] Y)
    (MNi MNk Gni : Z →L[ℝ] Z)
    (hKH : ∀ f, J (KH f) = Kl (I f))
    (hK : ∀ f, Kl (I f) = Tl (Sh f) - Sl (Th f))
    (hS : ∀ f, Sl (I f) = J (Sh f))
    (hT : ∀ f, Tl (I f) = J (Th f))
    (hMi : ∀ f, I (MHi f) = MLi (I f))
    (hMk : ∀ f, I (MHk f) = MLk (I f))
    (hMkN : ∀ v, J (MLk v) = MNk (J v))
    (hA : ∀ f, I (GAi f) = Th (MHi f) - MLi (Th f))
    (hGl : ∀ v, J (Gi v) = Sl (MLi v) - MNi (Sl v))
    (hGui : ∀ f, Gi (I f) = Sh (MHi f) - MLi (Sh f))
    (hGuk : ∀ f, Gk (I f) = Sh (MHk f) - MLk (Sh f))
    (hGHi : ∀ f, I (GHi f) = Gi (I f))
    (hGHk : ∀ f, I (GHk f) = Gk (I f))
    (hN : ∀ v, Tl (MLi v) - MNi (Tl v) = Gni (J v))
    (u : X) :
    J ((-(KH.comp (MHi.comp MHk)) - Sh.comp (GAi.comp MHk) - Gi.comp (Th.comp MHk) +
        Th.comp (GHi.comp MHk) + Th.comp (MHi.comp GHk)) u) =
      (-(MNi.comp (Kl.comp MLk)) + MNi.comp (Tl.comp Gk) - Gni.comp (MNk.comp Sl)) (I u) := by
  have hL : J ((-(KH.comp (MHi.comp MHk)) - Sh.comp (GAi.comp MHk) - Gi.comp (Th.comp MHk) +
        Th.comp (GHi.comp MHk) + Th.comp (MHi.comp GHk)) u) =
      -(J (KH (MHi (MHk u)))) - J (Sh (GAi (MHk u))) - J (Gi (Th (MHk u))) +
        J (Th (GHi (MHk u))) + J (Th (MHi (GHk u))) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, map_add, map_sub, map_neg]
  have hR : (-(MNi.comp (Kl.comp MLk)) + MNi.comp (Tl.comp Gk) - Gni.comp (MNk.comp Sl)) (I u) =
      -(MNi (Kl (MLk (I u)))) + MNi (Tl (Gk (I u))) - Gni (MNk (Sl (I u))) := by
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply]
  have e1 : J (KH (MHi (MHk u))) = Tl (Sh (MHi (MHk u))) - Sl (Th (MHi (MHk u))) :=
    (hKH _).trans (hK _)
  have e2 : J (Sh (GAi (MHk u))) = Sl (Th (MHi (MHk u))) - Sl (MLi (Th (MHk u))) := by
    rw [← hS, hA, map_sub]
  have e3 : J (Gi (Th (MHk u))) = Sl (MLi (Th (MHk u))) - MNi (Sl (Th (MHk u))) := hGl _
  have e4 : J (Th (GHi (MHk u))) = Tl (Sh (MHi (MHk u))) - Tl (MLi (Sh (MHk u))) := by
    rw [← hT, hGHi, hGui, map_sub]
  have e5 : J (Th (MHi (GHk u))) = Tl (MLi (Sh (MHk u))) - Tl (MLi (MLk (Sh u))) := by
    rw [← hT, hMi, hGHk, hGuk, map_sub, map_sub]
  have f1 : MNi (Kl (MLk (I u))) = MNi (Tl (Sh (MHk u))) - MNi (Sl (Th (MHk u))) := by
    rw [← hMk, hK, map_sub]
  have f2 : MNi (Tl (Gk (I u))) = MNi (Tl (Sh (MHk u))) - MNi (Tl (MLk (Sh u))) := by
    rw [hGuk, map_sub, map_sub]
  have f3 : Gni (MNk (Sl (I u))) = Tl (MLi (MLk (Sh u))) - MNi (Tl (MLk (Sh u))) := by
    rw [hS, ← hMkN, ← hN]
  rw [hL, hR, e1, e2, e3, e4, e5, f1, f2, f3]
  abel

/-! ### H9. Scalar profile budget: r^6 ≤ θ β. -/

lemma radial_pow_six_le_theta_mul_beta (r β θ : ℝ) (hr : 0 ≤ r) (hβ : 1 ≤ β)
    (hrθ : r * β ^ 2 ≤ θ) (hθ : θ ≤ 1) : r ^ 6 ≤ θ * β := by
  have hβ2 : 1 ≤ β ^ 2 := by nlinarith
  have hrβ : r ≤ r * β ^ 2 := le_mul_of_one_le_right hr hβ2
  have hrθ' : r ≤ θ := hrβ.trans hrθ
  have hr1 : r ≤ 1 := hrθ'.trans hθ
  have h6 : r ^ 6 ≤ r := pow_le_of_le_one hr hr1 (by norm_num)
  have hθ0 : 0 ≤ θ := hr.trans hrθ'
  exact h6.trans (hrθ'.trans (le_mul_of_one_le_right hθ0 hβ))

/-! ### Concrete actual operators. -/

-- Prop-valued completeness of the existing lp carriers.
local instance highRadialGainThreeHalfComplete : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance highRadialGainHalfComplete : CompleteSpace (SphereSobolev (1/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance highRadialGainNegativeHalfComplete : CompleteSpace (SphereSobolev (-(1/2 : ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

-- Reuse the existing canonical completeness of the CLM carriers explicitly.
local instance highRadialGainHighEndComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance
local instance highRadialGainHighHalfComplete :
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance
local instance highRadialGainHalfEndComplete :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by infer_instance
local instance highRadialGainHalfNegativeComplete :
    CompleteSpace (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := by infer_instance

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))))

local notation "Ihi" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "Jlo" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "CJ" => referenceRadialSkewProductJets g L y0 Φ B ε C ρ H a w hData hg Room
local notation "DJ" => referenceRadialSkewDerivativeJets g L y0 Φ B ε C ρ H a w hData hg Room
local notation "Dl" => referenceNormalizedAdjointHalfDefectFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room
local notation "Dh" => referenceNormalizedAdjointHighDefectFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  (Set.prod (Icc (0 : ℝ) 1) (Set.prod (Metric.closedBall y0 ρ) (Icc (-ρ) ρ))) Room
local notation "Sh" => referenceSharpRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-- Radial second Taylor remainder of the ACTUAL high primal multiplier commutator,
with the coefficient jet `Q` frozen inside the integral (H0). -/
def referenceHighSmoothMultiplierSecondRemainder
    (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) :=
  secondTaylorRemainder (fun t : ℝ => referenceHighSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r

local notation "GHr" => referenceHighSmoothMultiplierSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-! ### H2. High lift of the actual rotation second remainder. -/

lemma referenceSharpRadialRotationSecondRemainder_lower_inclusion
    (i j : Fin 3) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (Jlo).comp (referenceSharpRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r) =
      (referenceLowerRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j q y r).comp Ihi := by
  have hEmbed (t : ℝ) : ContDiffAt ℝ ∞ (fun τ : ℝ => (q,(y,τ))) t :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id)
  have hA (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (fun t : ℝ => referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,t))) (θ*r) := by
    have hp := hSegment θ hθ
    exact (contDiffAt_referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,θ*r)) hp.1 hp.2.1).comp
        (θ*r) (hEmbed (θ*r))
  have hB (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (fun t : ℝ => referenceLowerRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,t))) (θ*r) := by
    have hp := hSegment θ hθ
    exact (contDiffAt_referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,θ*r)) hp.2.2 hp.2.1).comp
        (θ*r) (hEmbed (θ*r))
  have hGerm (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t : ℝ => (Jlo).comp (referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,t)))) =ᶠ[𝓝 (θ*r)]
      (fun t : ℝ => (referenceLowerRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,t))).comp Ihi) := by
    have hNear : ∀ᶠ t : ℝ in 𝓝 (θ*r), (q,(y,t)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with t ht
    exact referenceLowerRadialRotationCommutatorL_upper_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,t)) ht.2.2 ht.1 ht.2.1
  have hT := secondTaylorRemainder_endpoint_intertwining
    (fun t : ℝ => referenceSharpRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,t)))
    (fun t : ℝ => referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,t)))
    Ihi Jlo r hA hB hGerm
  simpa only [referenceSharpRadialRotationSecondRemainder,
    referenceLowerRadialRotationSecondRemainder] using hT

/-! ### H3. High lift of the actual multiplier second remainder, on an explicit tube.
The tube entries are the literal hypotheses of the existing pointwise
`referenceHighSmoothMultiplierBoundaryCommutatorFamily_lower` and fixed-topology
lemmas; they are room conditions, not a gain/lift premise. -/

lemma referenceHighSmoothMultiplierSecondRemainder_lower_inclusion
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (Q : SmoothCoefficientJets 3) (q : ℝ) (y : R3) (r d lam Lam : ℝ) (hr : |r| < d)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hTube : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      (∀ z ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)‖ ≤ lam/4) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t))).IsInvertible ∧
      (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc) :
    (Ihi).comp (GHr Q q y r) =
      (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r).comp Ihi := by
  have hEmbed (t : ℝ) : ContDiffAt ℝ ∞ (fun τ : ℝ => (q,(y,τ))) t :=
    contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id)
  have hScaled (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : |θ*r| < d := by
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hMul : |θ*r| ≤ |r| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg r)).trans_eq (one_mul _)
    exact hMul.trans_lt hr
  have hA (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (fun t : ℝ => referenceHighSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) (θ*r) := by
    have hRoom := (hTube (θ*r) (hScaled θ hθ)).2.2.2
    unfold referenceGaugeNormalHighInvertibleLocus at hRoom
    exact (contDiffAt_referenceHighSmoothMultiplierBoundaryCommutatorFamily_fixed
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,θ*r)) hRoom.1 hRoom.2).comp
        (θ*r) (hEmbed (θ*r))
  have hB (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ ∞ (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) (θ*r) :=
    (contDiffAt_referenceSmoothMultiplierBoundaryCommutatorFamily_fixed
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q
        (q,(y,θ*r)) (hSegment θ hθ)).comp (θ*r) (hEmbed (θ*r))
  have hGerm (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun t : ℝ => (Ihi).comp (referenceHighSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t)))) =ᶠ[𝓝 (θ*r)]
      (fun t : ℝ => (referenceSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))).comp Ihi) := by
    have hOpen : IsOpen {t : ℝ | |t| < d} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hOpen.mem_nhds (hScaled θ hθ)] with t ht
    obtain ⟨hUE, hsmall, hWeak, -⟩ := hTube t ht
    exact ContinuousLinearMap.ext (fun f =>
      referenceHighSmoothMultiplierBoundaryCommutatorFamily_lower
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 Q (q,(y,t)) lam Lam
          hUE hsmall hWeak f)
  exact secondTaylorRemainder_endpoint_intertwining
    (fun t : ℝ => referenceHighSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t)))
    (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t)))
    Ihi Ihi r hA hB hGerm

/-! ### H4. The explicit actual HIGH Kbar : Hi → Half. -/

/-- High tangent part: same jets CJ/DJ and same (j,i) rotation order as the lower
`referenceRadialTangentSecondCommutator`. -/
def referenceRadialTangentSecondCommutatorHigh (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (((referenceSharpRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r).comp
        (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (CJ 3 i j (q,(y,r)))) -
      (sphereSobolevRotationL (3/2 : ℝ) j i).comp (GHr (CJ 3 i j (q,(y,r))) q y r)) -
      (Ihi).comp (GHr (DJ 3 i j (q,(y,r))) q y r))

/-- High defect part, built from the original normalized adjoint defects. -/
def referenceRadialDefectSecondCommutatorHigh (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  (Dl (q,(y,r))).comp (Sh q y r) - (Sh q y r).comp (Dh (q,(y,r)))

/-- The actual high gained radial adjoint/sharp commutator. -/
def referenceRadialAdjointSharpSecondCommutatorHigh (q : ℝ) (y : R3) (r : ℝ) :
    SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
  referenceRadialTangentSecondCommutatorHigh
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r +
  referenceRadialDefectSecondCommutatorHigh
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r

attribute [local irreducible] referenceRadialTangentSecondCommutatorHigh
  referenceRadialDefectSecondCommutatorHigh referenceRadialAdjointSharpSecondCommutatorHigh

/-! ### H5. Graph: J (KbarHigh u) = Kbar (I u). -/

theorem referenceRadialTangentSecondCommutatorHigh_lower_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hRoom : (q,(y,r)) ∈ Room.parameterRoom)
    (hAgree : (Ihi).comp (Dh (q,(y,r))) = (Dl (q,(y,r))).comp Ihi)
    (d lam Lam : ℝ) (hr : |r| < d)
    (hTube : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      (∀ z ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)‖ ≤ lam/4) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t))).IsInvertible ∧
      (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc)
    (u : SphereSobolev (3/2 : ℝ)) :
    Jlo (referenceRadialTangentSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
      referenceRadialTangentSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) := by
  have hIMap (Q : SmoothCoefficientJets 3) (v : SphereSobolev (3/2 : ℝ)) :
      Ihi (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q v) =
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (Ihi v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
        (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hS (v : SphereSobolev (3/2 : ℝ)) : Sl q y r (Ihi v) = Jlo (Sh q y r v) :=
    (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment)).symm
  have hMult (Q : SmoothCoefficientJets 3) (v : SphereSobolev (3/2 : ℝ)) :
      Ihi (GHr Q q y r v) =
        secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r (Ihi v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (referenceHighSmoothMultiplierSecondRemainder_lower_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg hKernel Q q y r d lam Lam
          hr hSegment hTube)
  have hRotSR (i j : Fin 3) (v : SphereSobolev (3/2 : ℝ)) :
      Jlo (referenceSharpRadialRotationSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r v) =
        referenceLowerRadialRotationSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r (Ihi v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      (referenceSharpRadialRotationSecondRemainder_lower_inclusion
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r hSegment)
  have hRot (i j : Fin 3) (v : SphereSobolev (3/2 : ℝ)) :
      Jlo (sphereSobolevRotationL (3/2 : ℝ) j i v) =
        sphereSobolevRotationL (1/2 : ℝ) j i (Ihi v) :=
    congrArg (fun T : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => T v)
      (sphereSobolevRotationL_threehalf_half_compatibility j i)
  have hTerm (i j : Fin 3) :
      Jlo (((referenceSharpRadialRotationSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r)
            (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (CJ 3 i j (q,(y,r))) u) -
          sphereSobolevRotationL (3/2 : ℝ) j i (GHr (CJ 3 i j (q,(y,r))) q y r u)) -
          Ihi (GHr (DJ 3 i j (q,(y,r))) q y r u)) =
        ((referenceLowerRadialRotationSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r)
            (nativeHalfCoefficientMulL hcalc hF hO hD τ0
              (smoothMultiplierLowerJets (CJ 3 i j (q,(y,r)))) (Ihi u)) -
          sphereSobolevRotationL (1/2 : ℝ) j i
            (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (CJ 3 i j (q,(y,r))) (q,(y,t))) r
                (Ihi u))) -
          Jlo (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (DJ 3 i j (q,(y,r))) (q,(y,t))) r
                (Ihi u)) := by
    have hFirst := (hRotSR i j
      (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (CJ 3 i j (q,(y,r))) u)).trans
        (congrArg (referenceLowerRadialRotationSecondRemainder
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r)
          (hIMap (CJ 3 i j (q,(y,r))) u))
    have hSecond := (hRot i j (GHr (CJ 3 i j (q,(y,r))) q y r u)).trans
      (congrArg (sphereSobolevRotationL (1/2 : ℝ) j i) (hMult (CJ 3 i j (q,(y,r))) u))
    have hThird := congrArg Jlo (hMult (DJ 3 i j (q,(y,r))) u)
    exact ((Jlo).map_sub _ _).trans
      (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
        (((Jlo).map_sub _ _).trans
          (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z) hFirst hSecond)) hThird)
  have hTanH : Jlo (referenceRadialTangentSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        Jlo (((referenceSharpRadialRotationSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r)
            (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (CJ 3 i j (q,(y,r))) u) -
          sphereSobolevRotationL (3/2 : ℝ) j i (GHr (CJ 3 i j (q,(y,r))) q y r u)) -
          Ihi (GHr (DJ 3 i j (q,(y,r))) q y r u)) := by
    simp only [referenceRadialTangentSecondCommutatorHigh, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, map_sum]
  have hTanL : referenceRadialTangentSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (((referenceLowerRadialRotationSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i q y r)
            (nativeHalfCoefficientMulL hcalc hF hO hD τ0
              (smoothMultiplierLowerJets (CJ 3 i j (q,(y,r)))) (Ihi u)) -
          sphereSobolevRotationL (1/2 : ℝ) j i
            (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (CJ 3 i j (q,(y,r))) (q,(y,t))) r
                (Ihi u))) -
          Jlo (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (DJ 3 i j (q,(y,r))) (q,(y,t))) r
                (Ihi u))) := by
    simp only [referenceRadialTangentSecondCommutator, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  have hTan : Jlo (referenceRadialTangentSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
      referenceRadialTangentSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) :=
    hTanH.trans ((Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => hTerm i j))).trans hTanL.symm)
  exact hTan

theorem referenceRadialDefectSecondCommutatorHigh_lower_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hRoom : (q,(y,r)) ∈ Room.parameterRoom)
    (hAgree : (Ihi).comp (Dh (q,(y,r))) = (Dl (q,(y,r))).comp Ihi)
    (d lam Lam : ℝ) (hr : |r| < d)
    (hTube : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      (∀ z ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)‖ ≤ lam/4) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t))).IsInvertible ∧
      (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc)
    (u : SphereSobolev (3/2 : ℝ)) :
    Jlo (referenceRadialDefectSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
      referenceRadialDefectSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) := by
  have hS (v : SphereSobolev (3/2 : ℝ)) : Sl q y r (Ihi v) = Jlo (Sh q y r v) :=
    (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A v)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment)).symm
  have hDef : Jlo (referenceRadialDefectSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
      referenceRadialDefectSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) := by
    have hG := referenceRadialDefectSecondCommutator_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hKernel
        q hq y hy r hSegment hRoom hAgree u
    have hExp : Jlo (referenceRadialDefectSecondCommutatorHigh
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
        Jlo (Dl (q,(y,r)) (Sh q y r u)) - Jlo (Sh q y r (Dh (q,(y,r)) u)) := by
      simp only [referenceRadialDefectSecondCommutatorHigh, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.comp_apply, map_sub]
    have hRight := hG.trans
      (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
        (rfl : Jlo (Dl (q,(y,r)) (Sh q y r u)) = Jlo (Dl (q,(y,r)) (Sh q y r u)))
        (hS (Dh (q,(y,r)) u)))
    exact hExp.trans hRight.symm
  exact hDef

theorem referenceRadialAdjointSharpSecondCommutatorHigh_lower_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hRoom : (q,(y,r)) ∈ Room.parameterRoom)
    (hAgree : (Ihi).comp (Dh (q,(y,r))) = (Dl (q,(y,r))).comp Ihi)
    (d lam Lam : ℝ) (hr : |r| < d)
    (hTube : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      (∀ z ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)‖ ≤ lam/4) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t))).IsInvertible ∧
      (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc)
    (u : SphereSobolev (3/2 : ℝ)) :
    Jlo (referenceRadialAdjointSharpSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
      referenceRadialAdjointSharpSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) := by
  have hTan := referenceRadialTangentSecondCommutatorHigh_lower_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel q hq y hy r hSegment hRoom hAgree d lam Lam hr hTube u
  have hDef := referenceRadialDefectSecondCommutatorHigh_lower_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel q hq y hy r hSegment hRoom hAgree d lam Lam hr hTube u
  have hSplit : Jlo (referenceRadialAdjointSharpSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
      Jlo (referenceRadialTangentSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) +
      Jlo (referenceRadialDefectSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) := by
    simp only [referenceRadialAdjointSharpSecondCommutatorHigh, ContinuousLinearMap.add_apply,
      map_add]
  have hSplitL : referenceRadialAdjointSharpSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) =
      referenceRadialTangentSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) +
      referenceRadialDefectSecondCommutator
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) := by
    simp only [referenceRadialAdjointSharpSecondCommutator, ContinuousLinearMap.add_apply]
  exact hSplit.trans
    ((congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x+z) hTan hDef).trans hSplitL.symm)

/-- Consequence: the high Kbar realizes the original `Tl Sh - Sl Th` graph. -/
theorem referenceRadialAdjointSharpSecondCommutatorHigh_remainder_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ ρ) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (hRoom : (q,(y,r)) ∈ Room.parameterRoom)
    (hAgree : (Ihi).comp (Dh (q,(y,r))) = (Dl (q,(y,r))).comp Ihi)
    (d lam Lam : ℝ) (hr : |r| < d)
    (hTube : ∀ t : ℝ, |t| < d →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      (∀ z ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)‖ ≤ lam/4) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t))).IsInvertible ∧
      (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc)
    (u : SphereSobolev (3/2 : ℝ)) :
    Jlo (referenceRadialAdjointSharpSecondCommutatorHigh
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
      (secondTaylorRemainder (fun t : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) (Sh q y r u) -
      Sl q y r ((secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) r) u) :=
  (referenceRadialAdjointSharpSecondCommutatorHigh_lower_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
      q hq y hy r hSegment hRoom hAgree d lam Lam hr hTube u).trans
    (referenceRadialAdjointSharpSecondCommutator_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
        q hq y hy r hSegment hRoom hAgree u)

/-! ### H6. One uniform radial room from the ACTUAL finite physical-domain room.
The tube premise is discharged: UE = hz.1, hsmall = hz.2.1.1,
hWeak = isInvertible_referenceWeakDirichletEnergyFamily … lam hz.2.1, and the high
locus is hz.2.2.2.1. -/

theorem exists_reference_commonRadius_radialAdjointSharpSecondCommutatorHigh_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y : R3, ‖y-y0‖ ≤ ρ → ∀ r : ℝ, |r| ≤ d →
        ∀ u : SphereSobolev (3/2 : ℝ),
          Jlo (referenceRadialAdjointSharpSecondCommutatorHigh
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r u) =
            referenceRadialAdjointSharpSecondCommutator
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room q y r (Ihi u) := by
  obtain ⟨lam,Lam,d0,_,hd0,_,hRoom0⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  obtain ⟨d1,hd1,hd1ρ,hRoom1⟩ := exists_reference_commonRadius_high_defect_lower_graph_segment
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Room
  refine ⟨min d1 (d0/2), lt_min hd1 (half_pos hd0), (min_le_left _ _).trans hd1ρ, ?_⟩
  intro q hq y hy r hr u
  have hyBall : y ∈ closedBall y0 ρ := by
    simpa only [mem_closedBall,dist_eq_norm] using hy
  have hTube : ∀ t : ℝ, |t| < d0 →
      TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun z => a ((q,(y,t)),z)) lam Lam ∧
      (∀ z ∈ (ballOpens : Set R3),
        ‖conformalReferenceWeightedFramedDrift g L Φ H w ((q,(y,t)),z)‖ ≤ lam/4) ∧
      (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t))).IsInvertible ∧
      (q,(y,t)) ∈ referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc := by
    intro t ht
    have hz := hRoom0 (q,(y,t)) ⟨hq,hyBall,abs_le.mp ht.le⟩
    refine ⟨hz.1,hz.2.1.1,
      isInvertible_referenceWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc (q,(y,t)) lam hz.2.1,?_⟩
    unfold referenceGaugeNormalHighInvertibleLocus
    exact hz.2.2.2.1
  have hr1 : |r| ≤ d1 := hr.trans (min_le_left _ _)
  have hr0 : |r| < d0 := (hr.trans (min_le_right _ _)).trans_lt (by linarith)
  have hPoint := hRoom1 q hq y hy r hr1
  exact referenceRadialAdjointSharpSecondCommutatorHigh_lower_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
      q hq y hy r hPoint.1 hPoint.2.1 hPoint.2.2 d0 lam Lam hr0 hTube u

/-! ### H6'. Public upper multiplier graph (the inline `hUpper` of the Kbar source),
needed by the H8 instantiation as (hGui)/(hGuk). -/

lemma referenceSmoothMultiplierSecondRemainder_upper_graph
    (hKernel : UnitBallValueTraceKernel τ0) (Q : SmoothCoefficientJets 3)
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (v : SphereSobolev (3/2 : ℝ)) :
    secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r (Ihi v) =
      Sh q y r (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q v) -
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (Sh q y r v) := by
  have hS (zHi : SphereSobolev (3/2 : ℝ)) : Sl q y r (Ihi zHi) = Jlo (Sh q y r zHi) :=
    (congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A zHi)
      (referenceSharpRadialTraceSecondRemainder_lower_compatibility
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r hSegment)).symm
  have hIMap : Ihi (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q v) =
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (Ihi v) :=
    congrArg (fun A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) => A v)
      (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0 Q
        (smoothMultiplierLowerJets Q) (coefficientValue_smoothMultiplierLowerJets Q).symm)
  have hJMap (w : SphereSobolev (1/2 : ℝ)) :
      Jlo (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) w) =
        nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (Jlo w) :=
    congrArg (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) => A w)
      (nativeCoefficientMulL_half_negative_compatibility hcalc hF hO hD τ0
        (smoothMultiplierLowerJets Q))
  have hLower := referenceSmoothMultiplierSecondRemainder_lower_graph
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hKernel Q q y r hSegment (Ihi v)
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  change Jlo (secondTaylorRemainder (fun t : ℝ => referenceSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q (q,(y,t))) r (Ihi v)) =
      Jlo (Sh q y r (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q v) -
        nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (Sh q y r v))
  have hRight : Jlo (Sh q y r (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q v) -
      nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (Sh q y r v)) =
      Sl q y r (nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) (Ihi v)) -
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q)
        (Sl q y r (Ihi v)) :=
    ((Jlo).map_sub _ _).trans
      (congrArg₂ (fun x z : SphereSobolev (-(1/2 : ℝ)) => x-z)
        ((hS (nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 Q v)).symm.trans
          (congrArg (Sl q y r) hIMap))
        ((hJMap (Sh q y r v)).trans
          (congrArg (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
            (smoothMultiplierLowerJets Q)) (hS v).symm)))
  exact hLower.trans hRight.symm

/-! ### H7a. Generic compact-room operator-norm cap from joint continuity. -/

lemma exists_opNorm_bound_of_continuousOn_compact
    {P E F' : Type*} [TopologicalSpace P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (K : Set P) (hK : IsCompact K) (T : P → E →L[ℝ] F') (hT : ContinuousOn T K) :
    ∃ M : ℝ, ∀ p ∈ K, ‖T p‖ ≤ M :=
  hK.exists_bound_of_continuousOn hT

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.secondTaylorRemainder_endpoint_intertwining
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.adjacentGainedCommutator_high_lower_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.radial_pow_six_le_theta_mul_beta
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSharpRadialRotationSecondRemainder_lower_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceHighSmoothMultiplierSecondRemainder_lower_inclusion
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialTangentSecondCommutatorHigh
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDefectSecondCommutatorHigh
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialAdjointSharpSecondCommutatorHigh
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialAdjointSharpSecondCommutatorHigh_lower_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialAdjointSharpSecondCommutatorHigh_remainder_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_radialAdjointSharpSecondCommutatorHigh_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceSmoothMultiplierSecondRemainder_upper_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_opNorm_bound_of_continuousOn_compact
