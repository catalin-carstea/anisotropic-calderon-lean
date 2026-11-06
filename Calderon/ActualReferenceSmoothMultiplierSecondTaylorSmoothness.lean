import Calderon.ActualReferenceSmoothMultiplierJointTopology
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.LocalSmoothSignedTaylorRemainder

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier
variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
attribute [local irreducible] referenceSmoothMultiplierBoundaryCommutatorFamily
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily secondTaylorRemainder
  nativeHalfCoefficientMulL sphereSobolevInclusionL

lemma contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_of_segment
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (Km : Set R3) (hKm : IsCompact Km) (hmz : ∀ t x, x ∉ Km → m (t,x) = 0)
    (q : ℝ) (y : R3) (r : ℝ) (t : T)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, (q,(y,θ*r)) ∈
      referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      secondTaylorRemainder (fun tau : ℝ =>
        referenceSmoothMultiplierBoundaryCommutatorFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
            (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2)
            (z.1.1,(z.1.2.1,tau))) z.1.2.2) ((q,(y,r)),t) := by
  classical
  let F : ((ℝ × R3) × T) × ℝ →
      SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun u =>
    referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 (commonSupportCoefficientFamily 3 m hm Km hKm hmz u.1.2)
        (u.1.1.1,(u.1.1.2,u.2))
  let Ω : Set (((ℝ × R3) × T) × ℝ) := {u | (u.1.1.1,(u.1.1.2,u.2)) ∈
    referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0}
  have hΩ : IsOpen Ω := (isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).preimage
      (continuous_fst.fst.fst.prodMk (continuous_fst.fst.snd.prodMk continuous_snd))
  have hSmooth : ContDiffOn ℝ ∞ F Ω := by
    intro u hu
    have hi := (show (u.1.1.1,(u.1.1.2,u.2)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 from hu)
    unfold referenceRadialEndpointInvertibleLocus at hi
    have hB := contDiffAt_referenceSmoothMultiplierBoundaryCommutator_commonSupport_joint
      g L y0 Φ B ε C ρ H a w hData m hm Km hKm hmz hcalc hF hO hD τ0
        (u.1.1.1,(u.1.1.2,u.2)) u.1.2 hi.1 hi.2.1
    exact (hB.comp
      (f := fun v : ((ℝ × R3) × T) × ℝ => ((v.1.1.1,(v.1.1.2,v.2)),v.1.2)) u
      ((contDiffAt_fst.fst.fst.prodMk
        (contDiffAt_fst.fst.snd.prodMk contDiffAt_snd)).prodMk contDiffAt_fst.snd)).contDiffWithinAt
  have hR := contDiffAt_secondTaylorRemainder_joint_of_open_segment F Ω hΩ hSmooth
    ((q,y),t) r hSegment
  have hReorder : ContDiff ℝ ∞ (fun u : (ℝ × (R3 × ℝ)) × T =>
      (((u.1.1,u.1.2.1),u.2),u.1.2.2)) := by
    fun_prop
  simpa only [F,Function.comp_def] using
    hR.comp (f := fun u : (ℝ × (R3 × ℝ)) × T =>
      (((u.1.1,u.1.2.1),u.2),u.1.2.2)) ((q,(y,r)),t) hReorder.contDiffAt


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
