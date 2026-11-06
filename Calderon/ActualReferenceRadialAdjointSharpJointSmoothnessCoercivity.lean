import Calderon.ActualReferencePrimalCommutatorJets
import Calderon.ActualReferenceRadialAdjointSharpSecondCommutatorCoercivity
import Calderon.ActualReferenceSmoothMultiplierSecondTaylorSmoothness
import Calderon.ActualReferenceGaugeNormalHalfRemainder
import Calderon.ActualReferenceGaugeTangentReciprocalSkew
import Calderon.ActualReferenceRadialRotationCommutatorJointJets
import Calderon.ActualReferenceRadialEndpointInvertibleTopology
import Calderon.NativeSmoothMultiplierCommonSupportJets
import Calderon.CompactInverseDerivativeBounds

/-!
UNCOMPILED proof-development draft. Upfront mathematics and exact source identity:
/tmp/ActualRadialKbarJointSmoothness_20261023.md.

This file deliberately does not import ActualReferenceNormalizedDefectTopology,
ActualReferenceRotationSignedRemainderJets, or ActualReferenceSignedRemainderJets.
The narrow lower-endpoint proofs are reproduced from their concrete selected
owners. In particular the negative defect below is the ORIGINAL Kbar definition
`-realHalfOperatorAdjointL Dl`, not the old differently-parameterized extension.
No admission, new mathematical callback, or changed operator definition is used.
-/

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology ENNReal

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))

-- These prove completeness of the existing canonical lp structures; they do
-- not install a different norm, inner product, or mathematical data instance.
local instance radialKbarJointHalfCompleteSpace : CompleteSpace Half := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance radialKbarJointNegativeHalfCompleteSpace : CompleteSpace Neg := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-- Concrete lower signed remainder smoothness, without importing the
aggregate signed-remainder module or changing its actual lower family. -/
lemma contDiffAt_referenceLowerRadialTraceSecondRemainder_joint_of_segment
    (p : Pphys)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun u : Pphys => referenceLowerRadialTraceSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 u.1 u.2.1 u.2.2) p := by
  let F : (ℝ × R3) × ℝ → Half →L[ℝ] Neg := fun u =>
    referenceLowerRadialEndpointFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 (u.1.1,(u.1.2,u.2))
  let U : Set ((ℝ × R3) × ℝ) := {u | (u.1.1,(u.1.2,u.2)) ∈ Ω}
  have hU : IsOpen U := (isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).preimage
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hF : ContDiffOn ℝ ∞ F U := by
    intro u hu
    have hi : (u.1.1,(u.1.2,u.2)) ∈ Ω := hu
    unfold referenceRadialEndpointInvertibleLocus at hi
    have hEndpoint := contDiffAt_referenceLowerRadialEndpointFamily_of_isInvertible
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        (u.1.1,(u.1.2,u.2)) hi.2.2 hi.2.1
    exact (hEndpoint.comp
      (f := fun v : (ℝ × R3) × ℝ => (v.1.1,(v.1.2,v.2))) u
      (contDiffAt_fst.fst.prodMk
        (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hTaylor := contDiffAt_secondTaylorRemainder_joint_of_open_segment
    F U hU hF (p.1,p.2.1) p.2.2 hSegment
  simpa only [referenceLowerRadialTraceSecondRemainder, F, Function.comp_def] using
    hTaylor.comp (f := fun u : Pphys => ((u.1,u.2.1),u.2.2)) p
      ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)

/-- Only the actual lower rotation remainder is needed for Kbar. -/
private lemma contDiffAt_referenceLowerRadialRotationSecondRemainder_for_commutator_of_segment
    (i j : Fin 3) (p : Pphys)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun u : Pphys => referenceLowerRadialRotationSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j u.1 u.2.1 u.2.2) p := by
  let F : (ℝ × R3) × ℝ → Half →L[ℝ] Neg := fun u =>
    referenceLowerRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 i j (u.1.1,(u.1.2,u.2))
  let U : Set ((ℝ × R3) × ℝ) := {u | (u.1.1,(u.1.2,u.2)) ∈ Ω}
  have hU : IsOpen U := (isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).preimage
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hF : ContDiffOn ℝ ∞ F U := by
    intro u hu
    have hi : (u.1.1,(u.1.2,u.2)) ∈ Ω := hu
    unfold referenceRadialEndpointInvertibleLocus at hi
    have hRotation := contDiffAt_referenceLowerRadialRotationCommutatorL
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
        i j (u.1.1,(u.1.2,u.2)) hi.2.2 hi.2.1
    exact (hRotation.comp
      (f := fun v : (ℝ × R3) × ℝ => (v.1.1,(v.1.2,v.2))) u
      (contDiffAt_fst.fst.prodMk
        (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hTaylor := contDiffAt_secondTaylorRemainder_joint_of_open_segment
    F U hU hF (p.1,p.2.1) p.2.2 hSegment
  simpa only [referenceLowerRadialRotationSecondRemainder, F, Function.comp_def] using
    hTaylor.comp (f := fun u : Pphys => ((u.1,u.2.1),u.2.2)) p
      ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)

/-- First keep the coefficient parameter independent inside the actual primal
Taylor integral. Only after applying its joint smoothness theorem take (p,p). -/
private lemma contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_diagonal_of_segment
    (m : Pphys × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km)
    (hmz : ∀ t x, x ∉ Km → m (t,x) = 0)
    (p : Pphys)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun u : Pphys =>
      secondTaylorRemainder (fun τ : ℝ =>
        referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
            (commonSupportCoefficientFamily 3 m hm Km hKm hmz u)
            (u.1,(u.2.1,τ))) u.2.2) p := by
  have hJoint := contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_of_segment
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      m hm Km hKm hmz p.1 p.2.1 p.2.2 p hSegment
  simpa only [Function.comp_def] using
    hJoint.comp (f := fun u : Pphys => (u,u)) p
      (contDiffAt_id.prodMk contDiffAt_id)

variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a (Set.prod (Icc (0 : ℝ) 1) (Set.prod (closedBall y0 ρ) (Icc (-ρ) ρ))))
include Room

local notation "CJ" => referenceRadialSkewProductJets
  g L y0 Φ B ε C ρ H a w hData hg Room
local notation "DJ" => referenceRadialSkewDerivativeJets
  g L y0 Φ B ε C ρ H a w hData hg Room
local notation "Dl" => referenceNormalizedAdjointHalfDefectFamily
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (closedBall y0 ρ) (Icc (-ρ) ρ))) Room
local notation "Sl" => referenceLowerRadialTraceSecondRemainder
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0

/-- The original CJ lower jets are exactly the order-two common-support jets,
not a newly chosen extension with merely matching sphere values. -/
private lemma contDiff_referenceRadialSkewProductHalfMultiplier (i j : Fin 3) :
    ContDiff ℝ ∞ (fun u : Pphys => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (CJ 3 i j u))) := by
  simpa only [referenceRadialSkewProductJets, smoothMultiplierLowerJets_commonSupport] using
    contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (referenceRadialSkewProductCoefficient g L y0 Φ ρ a Room i j)
      (contDiff_referenceRadialSkewProductCoefficient
        g L y0 Φ B ε C ρ H a w hData hg Room i j)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (referenceRadialSkewProductCoefficient_support
        g L y0 Φ B ε C ρ H a w hData Room i j)

/-- The complete original tangent part is jointly smooth. The literal CJ/DJ
coefficient remains frozen inside each radial second Taylor remainder. -/
private lemma contDiffAt_referenceRadialTangentSecondCommutator_of_segment
    (p : Pphys)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun u : Pphys => referenceRadialTangentSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
        u.1 u.2.1 u.2.2) p := by
  have hRotation (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun u : Pphys => referenceLowerRadialRotationSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i u.1 u.2.1 u.2.2) p :=
    contDiffAt_referenceLowerRadialRotationSecondRemainder_for_commutator_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 j i p hSegment
  have hCoefficient (i j : Fin 3) : ContDiffAt ℝ ∞
      (fun u : Pphys => nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (smoothMultiplierLowerJets (CJ 3 i j u))) p :=
    (contDiff_referenceRadialSkewProductHalfMultiplier
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room i j).contDiffAt
  have hCJ (i j : Fin 3) : ContDiffAt ℝ ∞ (fun u : Pphys =>
      secondTaylorRemainder (fun τ : ℝ =>
        referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
            (CJ 3 i j u) (u.1,(u.2.1,τ))) u.2.2) p := by
    simpa only [referenceRadialSkewProductJets] using
      contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_diagonal_of_segment
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
          (referenceRadialSkewProductCoefficient g L y0 Φ ρ a Room i j)
          (contDiff_referenceRadialSkewProductCoefficient
            g L y0 Φ B ε C ρ H a w hData hg Room i j)
          (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
          (referenceRadialSkewProductCoefficient_support
            g L y0 Φ B ε C ρ H a w hData Room i j) p hSegment
  have hDJ (i j : Fin 3) : ContDiffAt ℝ ∞ (fun u : Pphys =>
      secondTaylorRemainder (fun τ : ℝ =>
        referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
            (DJ 3 i j u) (u.1,(u.2.1,τ))) u.2.2) p := by
    simpa only [referenceRadialSkewDerivativeJets] using
      contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_diagonal_of_segment
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
          (referenceRadialSkewDerivativeCoefficient g L y0 Φ ρ a Room i j)
          (contDiff_referenceRadialSkewDerivativeCoefficient
            g L y0 Φ B ε C ρ H a w hData hg Room i j)
          (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
          (referenceRadialSkewDerivativeCoefficient_support
            g L y0 Φ B ε C ρ H a w hData hg Room i j) p hSegment
  unfold referenceRadialTangentSecondCommutator
  apply ContDiffAt.sum
  intro i hi
  apply ContDiffAt.sum
  intro j hj
  exact (((hRotation i j).clm_comp (hCoefficient i j)).sub
    (contDiffAt_const.clm_comp (hCJ i j))).sub
      (contDiffAt_const.clm_comp (hDJ i j))

/-- Smoothness of the actual defect commutator retains the negative adjoint
and both original composition orders. No skew-extension replacement is made. -/
private lemma contDiffAt_referenceRadialDefectSecondCommutator_of_segment
    (p : Pphys)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun u : Pphys => referenceRadialDefectSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
        u.1 u.2.1 u.2.2) p := by
  have hLower : ContDiffAt ℝ ∞ (fun u : Pphys => Sl u.1 u.2.1 u.2.2) p :=
    contDiffAt_referenceLowerRadialTraceSecondRemainder_joint_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p hSegment
  have hDefect : ContDiffAt ℝ ∞ Dl p := by
    unfold referenceNormalizedAdjointHalfDefectFamily
    exact (contDiffAt_referenceGaugeNormalHalfSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        p.1 p.2.1 p.2.2 hSegment).add
      (contDiff_referenceGaugeTangentReciprocalResidualHalfFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 (Set.prod (Icc (0 : ℝ) 1) (Set.prod (closedBall y0 ρ) (Icc (-ρ) ρ))) Room).contDiffAt
  have hNegative : ContDiffAt ℝ ∞
      (fun u : Pphys => -realHalfOperatorAdjointL (Dl u)) p :=
    contDiffAt_neg_realHalfOperatorAdjointL_comp Dl p hDefect
  simpa only [referenceRadialDefectSecondCommutator,
    referenceNormalizedAdjointNegativeDefectFamily, Function.comp_def] using
    (hNegative.clm_comp hLower).sub (hLower.clm_comp hDefect)

/-- Joint ordinary smoothness of the original genuine429 Half-to-Neg Kbar.
hreg and hKernel are retained from its original caller context; the local
analytic proof only needs the concrete signed inverse segment and SAME Room. -/
theorem contDiffAt_referenceRadialAdjointSharpSecondCommutator_of_segment
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (p : Pphys)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (p.1,(p.2.1,θ*p.2.2)) ∈ Ω) :
    ContDiffAt ℝ ∞ (fun u : Pphys => referenceRadialAdjointSharpSecondCommutator
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
        u.1 u.2.1 u.2.2) p := by
  have hTangent := contDiffAt_referenceRadialTangentSecondCommutator_of_segment
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room p hSegment
  have hDefect := contDiffAt_referenceRadialDefectSecondCommutator_of_segment
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room p hSegment
  simpa only [referenceRadialAdjointSharpSecondCommutator] using hTangent.add hDefect


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
