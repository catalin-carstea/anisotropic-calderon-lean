import Calderon.ActualReferenceDegreeGainedHighFamily
import Calderon.ActualReferenceDegreeHalfChosenRadialValueCorrespondence
import Calderon.SignedTaylorOperatorIntertwining
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.SequenceLpNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData

/-! Full upfront: high-degree-rotation-author-oct15-v001/
EXPANSION-actual-degree-gained-high-signed-remainder-v133.md. SAME named half remainder. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local instance : CompleteSpace (SphereSobolev (1/2:ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

def referenceRadialDegreeCommutatorGainedHighSecondRemainder
    (q : ℝ) (y : R3) (r : ℝ) : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  secondTaylorRemainder (fun z : ℝ => referenceRadialDegreeCommutatorGainedHighFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,z))) r

attribute [local irreducible] referenceRadialDegreeCommutatorGainedHighFamily
  referenceRadialDegreeCommutatorGainedHighSecondRemainder referenceRadialDegreeCommutatorHalfFamily
  referenceRadialDegreeCommutatorHalfSecondRemainder referenceRadialEndpointInvertibleLocus
  sphereSobolevInclusionL secondTaylorRemainder

lemma referenceRadialDegreeCommutatorGainedHighSecondRemainder_lower_compatibility
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0:ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (referenceRadialDegreeCommutatorGainedHighSecondRemainder
        g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r) =
    (referenceRadialDegreeCommutatorHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r).comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  let U : ℝ → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun z =>
    referenceRadialDegreeCommutatorGainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,z))
  let A : ℝ → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun z =>
    referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  have hUS (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ U (θ*r) :=
    (contDiffAt_referenceRadialDegreeCommutatorGainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,θ*r)) (hSegment θ hθ)).comp
        (f := fun z : ℝ => (q,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hAS (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ A (θ*r) :=
    (contDiffAt_referenceRadialDegreeCommutatorHalfFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,θ*r)) (hSegment θ hθ)).comp
        (f := fun z : ℝ => (q,(y,z))) (θ*r)
        (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) :
      (fun z => J.comp (U z)) =ᶠ[𝓝 (θ*r)] (fun z => (A z).comp I) := by
    have hNear : ∀ᶠ z : ℝ in 𝓝 (θ*r), (q,(y,z)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with z hz
    exact referenceRadialDegreeCommutatorGainedHighFamily_lower_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (q,(y,z)) hz
  have hLaw := secondTaylorRemainder_operator_intertwining
    (X := SphereSobolev (3/2:ℝ)) (Y := SphereSobolev (1/2:ℝ)) (Z := SphereSobolev (-(1/2:ℝ)))
  simp (config := { instances := true }) only [real_nontriviallyNormedField_normedField_eq,
    sequenceLp_normedAddCommGroup_addCommMonoid_eq_natural,sequenceLp_normedSpace_module_eq_natural,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hLaw
  have hTransport : J.comp (secondTaylorRemainder U r) = (secondTaylorRemainder A r).comp I :=
    hLaw U A I J r hUS hAS hEq
  have hHigh : referenceRadialDegreeCommutatorGainedHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r = secondTaylorRemainder U r := by
    unfold referenceRadialDegreeCommutatorGainedHighSecondRemainder
    rfl
  have hNamed : referenceRadialDegreeCommutatorHalfSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 q y r = secondTaylorRemainder A r :=
    referenceRadialDegreeCommutatorHalfSecondRemainder_eq_chosen_remainder
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 q y r hSegment
  exact (congrArg (fun T : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => J.comp T) hHigh).trans
    (hTransport.trans (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) =>
      T.comp I) hNamed).symm)

lemma contDiffAt_referenceRadialDegreeCommutatorGainedHighSecondRemainder_of_segment
    (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0:ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) => referenceRadialDegreeCommutatorGainedHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 z.1 z.2.1 z.2.2) (q,(y,r)) := by
  let F : (ℝ × R3) × ℝ → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) := fun z =>
    referenceRadialDegreeCommutatorGainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (z.1.1,(z.1.2,z.2))
  let Ω : Set ((ℝ × R3) × ℝ) := {z | (z.1.1,(z.1.2,z.2)) ∈
    referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0}
  have hΩ : IsOpen Ω := (isOpen_referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).preimage
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hFSmooth : ContDiffOn ℝ ∞ F Ω := by
    intro z hz
    have hi : (z.1.1,(z.1.2,z.2)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 := hz
    exact ((contDiffAt_referenceRadialDegreeCommutatorGainedHighFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0 (z.1.1,(z.1.2,z.2)) hi).comp
      (f := fun v : (ℝ × R3) × ℝ => (v.1.1,(v.1.2,v.2))) z
        (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))).contDiffWithinAt
  have hR : ContDiffAt ℝ ∞
      (fun z : (ℝ × R3) × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) ((q,y),r) :=
    contDiffAt_secondTaylorRemainder_joint_of_open_segment F Ω hΩ hFSmooth (q,y) r hSegment
  have hOut := hR.comp (f := fun z : ℝ × (R3 × ℝ) => ((z.1,z.2.1),z.2.2)) (q,(y,r))
    ((contDiffAt_fst.prodMk contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  simpa only [referenceRadialDegreeCommutatorGainedHighSecondRemainder,Function.comp_def,F] using hOut

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorGainedHighSecondRemainder
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceRadialDegreeCommutatorGainedHighSecondRemainder_lower_compatibility
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceRadialDegreeCommutatorGainedHighSecondRemainder_of_segment
