import Calderon.ActualAdjointSmoothMultiplierExtendedCenterJointGainTransferJointRegularity
import Calderon.CompactWithinJetBounds
import Calderon.ActualAdjointSmoothMultiplierHalfSignedTaylorGraphTransferJointRegularity
import Calderon.ActualAdjointHighCommonSupportSecondTaylorSmoothnessTransferJointRegularity
import Calderon.SphereSobolevBalancedDualInterpolationLinear
import Calderon.SphereSobolevBalancedDualInterpolationValueBound
import Calderon.SphereSobolevBalancedDualEndpointStructure
import Calderon.SphereSobolevBesselOrderCompatibility
import Calderon.SmoothKernelCodomainStructureTransport
import Calderon.CollaboratorUnitBallValueTraceKernelOct17
import Calderon.CompactInverseDerivativeBounds
import Calderon.CoefficientFirstJetsCommonSupport
import Calderon.ActualJacobiHighPhysicalRoomTransferJointRegularity
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic
open NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
open OAI.AnisotropicCalderon.SmoothKernelCodomainStructureTransport

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
  [FiniteDimensional ℝ T]

attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  realHalfOperatorAdjointL sphereSobolevInclusionL

theorem exists_reference_commonRadius_adjointSmoothMultiplier_canonical_joint_jets
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧
      ∀ (m : T × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
        (Km : Set R3) (hKm : IsCompact Km)
        (hmz : ∀ t x, x ∉ Km → m (t,x) = 0),
      let S : Set ((ℝ × (R3 × ℝ)) × T) :=
        (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ×ˢ univ
      let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
      let J := sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
      let Gh : ((ℝ × (R3 × ℝ)) × T) →
          SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ) := fun z =>
        secondTaylorRemainder (fun tau : ℝ =>
          referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
              (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2)
              (z.1.1,(z.1.2.1,tau))) z.1.2.2
      let GS : ((ℝ × (R3 × ℝ)) × T) →
          SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) := fun z =>
        secondTaylorRemainder (fun tau : ℝ =>
          referenceSmoothMultiplierBoundaryCommutatorFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
              (commonSupportCoefficientFamily 3 m hm Km hKm hmz z.2)
              (z.1.1,(z.1.2.1,tau))) z.1.2.2
      let Gn := fun z => -realHalfOperatorAdjointL (GS z)
      ∃ G : ((ℝ × (R3 × ℝ)) × T) →
          SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ),
        ContDiffOn ℝ ∞ G S ∧
        (∀ z ∈ S,
          (∀ u, G z (I u) = I (Gh z u)) ∧
          (∀ v, J (G z v) = Gn z (J v)) ∧
          ‖G z‖ ≤ max ‖Gh z‖ ‖Gn z‖) ∧
        (∀ Kt : Set T, IsCompact Kt → ∀ N : ℕ,
          ∃ M : ℝ, 0 ≤ M ∧
            ∀ z ∈ (Icc (0 : ℝ) 1 ×ˢ
                (closedBall y0 ρ ×ˢ Icc (-d) d)) ×ˢ Kt,
              ∀ n : ℕ, n ≤ N →
                ‖iteratedFDerivWithin ℝ n G S z‖ ≤ M) := by
  classical
  have hρ : 0 < ρ := hData.1.2.1
  have hWitness :=
    exists_reference_commonRadius_adjointSmoothMultiplier_extended_center_joint_jets
      (T := T) g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0
  rcases hWitness with ⟨d,hd,hdρ,hd1,hFamily⟩
  refine ⟨d,hd,hdρ,hd1,?_⟩
  intro m hm Km hKm hmz S I J Gh GS Gn
  let Sext : Set ((ℝ × (R3 × ℝ)) × T) :=
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 (3*ρ/2) ×ˢ Icc (-d) d)) ×ˢ univ
  have hFamilym := hFamily m hm Km hKm hmz
  rcases hFamilym with ⟨G,hGext,hGraphExt,_hCapsExt⟩
  have hSub : S ⊆ Sext := by
    intro z hz
    exact ⟨⟨hz.1.1,closedBall_subset_closedBall (by linarith) hz.1.2.1,hz.1.2.2⟩,hz.2⟩
  have hG : ContDiffOn ℝ ∞ G S := hGext.mono hSub
  refine ⟨G,hG,(fun z hz => hGraphExt z (hSub hz)),?_⟩
  intro Kt hKt N
  exact exists_nonneg_bound_sphereSobolev_middle_jets_on_physical_tube
    y0 ρ d hρ hd S rfl G hG Kt hKt N
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
