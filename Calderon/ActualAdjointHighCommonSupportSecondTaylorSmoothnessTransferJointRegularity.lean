import Calderon.ActualReferenceHighSkewReciprocalDictionaryTransferJointRegularity
import Calderon.ActualAdjointHighCommonSupportGainTopologyTransferJointRegularity
import Calderon.ActualAdjointHighSmoothMultiplierSignedTaylorGraphTransferJointRegularity
import Calderon.ActualJacobiCommonSupportMultiplierGerms
import Calderon.ActualReferencePairedHighRadialRemainderLocalSmoothness
import Calderon.ActualJacobiHighPhysicalRoomTransferJointRegularity
import Calderon.IteratedFDerivClosedBallCongruence
import Calderon.CompactInverseDerivativeBounds
import Calderon.LocalSmoothSignedTaylorRemainder

set_option autoImplicit false
noncomputable section
open Set Filter Function Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier

local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Xhigh" => SphereSobolev (3/2 : ℝ)
local notation "Yhalf" => SphereSobolev (1/2 : ℝ)

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceGaugeNormalHighInvertibleLocus referenceAdjointThreeHalfRadialFamily
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily secondTaylorRemainder
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL sphereSobolevInclusionL

local instance actualAdjointHighCommonSupportSecondTaylorSmoothnessCompleteSpaceThreeHalf :
    CompleteSpace Xhigh := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance actualAdjointHighCommonSupportSecondTaylorSmoothnessCompleteSpaceHalf :
    CompleteSpace Yhalf := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance actualAdjointHighCommonSupportSecondTaylorSmoothnessCompleteSpaceHighEnd :
    CompleteSpace (Xhigh →L[ℝ] Xhigh) := by infer_instance
local instance actualAdjointHighCommonSupportSecondTaylorSmoothnessCompleteSpaceHighHalf :
    CompleteSpace (Xhigh →L[ℝ] Yhalf) := by infer_instance

lemma contDiffAt_referenceAdjointHighCommonSupportSecondRemainder_of_segment
    {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x)=0)
    (q : ℝ) (y : R3) (r : ℝ) (t : T)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc) :
    ContDiffAt ℝ ∞ (fun z : Pphys × T => secondTaylorRemainder (fun τ : ℝ =>
      referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2)
          (z.1.1,(z.1.2.1,τ))) z.1.2.2) ((q,(y,r)),t) := by
  let F : (((ℝ × R3) × T) × ℝ) → Xhigh →L[ℝ] Xhigh := fun z =>
    referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.1.2)
        (z.1.1.1,(z.1.1.2,z.2))
  let Ω : Set (((ℝ × R3) × T) × ℝ) := {z | (z.1.1.1,(z.1.1.2,z.2)) ∈
    referenceGaugeNormalHighInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc}
  have hΩ : IsOpen Ω :=
    (isOpen_referenceGaugeNormalHighInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc).preimage
      (continuous_fst.fst.fst.prodMk (continuous_fst.fst.snd.prodMk continuous_snd))
  have hSmooth : ContDiffOn ℝ ∞ F Ω := by
    intro z hz
    have hJoint := contDiffAt_referenceHighAdjointSmoothMultiplierBoundaryCommutator_commonSupport_joint
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      m hm Km hKm hmz (z.1.1.1,(z.1.1.2,z.2)) z.1.2 hz
    exact (hJoint.comp
      (f := fun u : (((ℝ × R3) × T) × ℝ) => ((u.1.1.1,(u.1.1.2,u.2)),u.1.2)) z
      ((contDiffAt_fst.fst.fst.prodMk
        (contDiffAt_fst.fst.snd.prodMk contDiffAt_snd)).prodMk contDiffAt_fst.snd)).contDiffWithinAt
  have hR := contDiffAt_secondTaylorRemainder_joint_of_open_segment
    F Ω hΩ hSmooth ((q,y),t) r hSegment
  have hReorder : ContDiff ℝ ∞ (fun z : Pphys × T => (((z.1.1,z.1.2.1),z.2),z.1.2.2)) := by
    fun_prop
  simpa only [F,Function.comp_def] using
    hR.comp (f := fun z : Pphys × T => (((z.1.1,z.1.2.1),z.2),z.1.2.2)) ((q,(y,r)),t)
      hReorder.contDiffAt


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceAdjointHighCommonSupportSecondRemainder_of_segment
