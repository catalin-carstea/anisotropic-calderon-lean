import Calderon.SphereSobolevCompatibleMiddlePhysicalTubeJets
import Calderon.ActualAdjointSmoothMultiplierExtendedCenterSmoothRoomTransferJointRegularity
import Calderon.SphereSobolevPhysicalTubeJetBounds
import Calderon.ActualAdjointSmoothMultiplierExtendedRoomCompatibilityTransferJointRegularity
import Calderon.SphereSobolevBalancedDualSmoothMiddle
import Calderon.ActualReferenceExtendedCenterInverseRoom
import Calderon.ActualReferenceSmoothMultiplierSecondTaylorSmoothness
import Calderon.ActualAdjointSmoothMultiplierExtendedRoomCompatibilityTransferJointRegularity
import Calderon.SphereSobolevBalancedDualSmoothMiddle
import Calderon.CompactWithinJetBounds
-- Modular proof of the extended-centre regularity statement.
import Calderon.WeightedCommonSupportCoefficients
import Calderon.MixedLinearDriftBounds
import Calderon.CompactParameterReferenceWeakDriftCoercivity
import Calderon.ActualReferenceStrongRoom
import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualReferenceGaugeNormalHighCommutatorDefinition
import Calderon.ActualHighAdjointSmoothMultiplierBoundaryGraph
import Calderon.SignedTaylorIncludedCommutatorTransport
import Calderon.ActualAdjointRadialSmoothMultiplierSignedTaylorFactor
import Calderon.ActualReferenceAdjointSignedRemainderCompatibility
import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.ActualAdjointHighCommonSupportGainTopologyTransferJointRegularity
import Calderon.ActualAdjointHighCommonSupportSecondTaylorSmoothnessTransferJointRegularity
import Calderon.NativeOrderOneCoefficientMultiplier
import Calderon.SphereSobolevBalancedDualInterpolationLinear
import Calderon.SphereSobolevBalancedDualInterpolationValueBound
import Calderon.SphereSobolevBalancedDualEndpointStructure
import Calderon.SphereSobolevBesselOrderCompatibility
import Calderon.SmoothKernelCodomainStructureTransport
import Calderon.CoefficientFirstJetsCommonSupport
import Calderon.CollaboratorUnitBallValueTraceKernelOct17
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator
open NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
open OAI.AnisotropicCalderon.SmoothKernelCodomainRestriction
open OAI.AnisotropicCalderon.SmoothKernelCodomainStructureTransport

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]
  [FiniteDimensional ℝ T]

-- Keep these definitions locally irreducible, as in the sibling files; this adds no
-- instance.
attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  realHalfOperatorAdjointL sphereSobolevInclusionL

theorem exists_reference_commonRadius_adjointSmoothMultiplier_extended_center_joint_jets
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
        (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 (3*ρ/2) ×ˢ Icc (-d) d)) ×ˢ univ
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
                (closedBall y0 (3*ρ/2) ×ˢ Icc (-d) d)) ×ˢ Kt,
              ∀ n : ℕ, n ≤ N →
                ‖iteratedFDerivWithin ℝ n G S z‖ ≤ M) := by
  classical
  have hρ : 0 < ρ := hData.1.2.1
  have hWitness := exists_reference_adjointSmoothMultiplier_extended_center_smooth_room
    (T := T) g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0
  rcases hWitness with ⟨lam,Lam,d0,d,hd,hdρ,hd1,hdd0strict,hRoom,hSmooth⟩
  refine ⟨d,hd,hdρ,hd1,?_⟩
  intro m hm Km hKm hmz S I J Gh GS Gn
  have hSmoothm := hSmooth m hm Km hKm hmz
  have hGh : ContDiffOn ℝ ∞ Gh S := hSmoothm.1
  have hGn : ContDiffOn ℝ ∞ Gn S := hSmoothm.2
  have hCompatible : ∀ z ∈ S, ∀ u : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (Gh z u) =
        Gn z (sphereSobolevInclusionL (3/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) u) := by
    rintro ⟨⟨q,y,r⟩,t⟩ hz u
    exact referenceAdjointSmoothMultiplierSecondRemainder_compatible_of_extended_room
      g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0
      lam Lam d0 d hdd0strict hRoom m hm Km hKm hmz
      q hz.1.1 y hz.1.2.1 r (abs_le.mpr hz.1.2.2) t u
  have hb : 0 < 3*ρ/2 := by positivity
  exact exists_sphereSobolev_compatible_middle_jets_on_physical_tube
    (T := T) y0 (3*ρ/2) d hb hd S rfl Gh Gn hGh hGn hCompatible
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
