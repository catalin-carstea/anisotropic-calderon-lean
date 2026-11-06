import Calderon.FinitePairedEndpointJetBounds
import Calderon.ActualReferenceLowerRotationCommutator
import Calderon.ActualReferenceUpperRotationCommutatorJointJets
import Calderon.LocalRadialDerivative
import Calderon.CompactInverseDerivativeBounds
import Calderon.ActualReferenceRadialEndpointOpenLocus

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation

/-! Full upfront argument is EXPANSION-v002.json in this immutable author directory.
Both actual angular endpoint derivatives retain their original Sobolev orders. The radius below
is selected from the original three-inverse locus before N and before all nine pairs. -/

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

lemma contDiffAt_referenceLowerRadialRotationCommutatorL
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (i j : Fin 3) (p : ℝ × (R3 × ℝ))
    (hNormal : (referenceNormalBoundaryMultiplierFamily g L y0 Φ B ε C ρ H a w hData
      hcalc hF hO hD τ0 p).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞
      (referenceLowerRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p := by
  let Q : ℝ × (ℝ × (R3 × ℝ)) →
      SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun z =>
    referenceRotationLowerRadialEndpointFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j z
  let F : (ℝ × (R3 × ℝ)) × ℝ →
      SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := fun z => Q (z.2,z.1)
  have hQ : ContDiffAt ℝ ∞ Q (0,p) :=
    contDiffAt_referenceRotationLowerRadialEndpointFamily_joint_zero_angle
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hNormal hWeak
  have hF : ContDiffAt ℝ ∞ F (p,0) :=
    hQ.comp (p,0) (contDiffAt_snd.prodMk contDiffAt_fst)
  have hG : ContDiffAt ℝ ∞ (fun p' : ℝ × (R3 × ℝ) => radialFirstDerivative F (p',0)) p :=
    (contDiffAt_radialFirstDerivative F (p,0) hF).comp p
      (contDiffAt_id.prodMk contDiffAt_const)
  have hNearby : ∀ᶠ z in 𝓝 (p,(0:ℝ)), DifferentiableAt ℝ F z := by
    filter_upwards [(hF.of_le (show (1:ℕ∞ω) ≤ (∞:ℕ∞ω) by simp)).eventually (by simp)] with z hz
    exact hz.differentiableAt (by norm_num)
  have hNearbySlice := (continuous_id.prodMk (continuous_const (y := (0:ℝ)))).continuousAt.eventually hNearby
  apply hG.congr_of_eventuallyEq
  filter_upwards [hNearbySlice] with p' hp'
  change deriv (fun θ : ℝ => F (p',θ)) 0 = radialFirstDerivative F (p',0)
  exact deriv_radialSlice_of_differentiableAt F p' 0 hp'

attribute [local irreducible] referenceLowerRadialRotationCommutatorL
  referenceSharpRadialRotationCommutatorL

theorem exists_reference_commonRadius_radialRotationCommutator_endpoint_jets
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ N : ℕ,
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ p ∈ Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ),
          p ∈ referenceRadialEndpointInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
          ∀ i j : Fin 3,
            ContDiffAt ℝ ∞ (referenceLowerRadialRotationCommutatorL
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p ∧
            ContDiffAt ℝ ∞ (referenceSharpRadialRotationCommutatorL
              g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p ∧
            ∀ k : ℕ, k ≤ N →
              ‖iteratedFDeriv ℝ k (referenceLowerRadialRotationCommutatorL
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p‖ ≤ M ∧
              ‖iteratedFDeriv ℝ k (referenceSharpRadialRotationCommutatorL
                g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j) p‖ ≤ M := by
  let K : ℝ → Set (ℝ × (R3 × ℝ)) := fun δ =>
    Icc (0:ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)
  let Ω : Set (ℝ × (R3 × ℝ)) :=
    referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let C0 : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
      SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    referenceLowerRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let C1 : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    referenceSharpRadialRotationCommutatorL g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hK : ∀ δ : ℝ, IsCompact (K δ) :=
    fun δ => isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  have hRadius : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ K δ ⊆ Ω :=
    exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  refine Exists.elim hRadius ?_
  intro δ hChosen
  have hδ : 0 < δ := And.left hChosen
  have hδρ : δ ≤ ρ := And.left (And.right hChosen)
  have hRoom : K δ ⊆ Ω := And.right (And.right hChosen)
  have hRoomSmooth : ∀ p ∈ K δ, p ∈ Ω ∧ ∀ i j : Fin 3,
      ContDiffAt ℝ ∞ (C0 i j) p ∧ ContDiffAt ℝ ∞ (C1 i j) p := by
    intro p hp
    have hi := hRoom hp
    apply And.intro hi
    intro i j
    exact And.intro
      (contDiffAt_referenceLowerRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hi.2.2 hi.2.1)
      (contDiffAt_referenceSharpRadialRotationCommutatorL
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j p hi.1 hi.2.1)
  have hAugmented : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ p ∈ K δ,
      p ∈ Ω ∧ ∀ i j : Fin 3, ContDiffAt ℝ ∞ (C0 i j) p ∧ ContDiffAt ℝ ∞ (C1 i j) p :=
    Exists.intro δ (And.intro hδ (And.intro hδρ hRoomSmooth))
  exact exists_commonRadius_finite_pair_endpoint_jets C0 C1 K hK (fun p => p ∈ Ω) ρ hAugmented

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceLowerRadialRotationCommutatorL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_radialRotationCommutator_endpoint_jets

