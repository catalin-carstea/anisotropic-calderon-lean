-- ADVISORY PROPOSAL (Claude consult 2026-10-23). NOT COMPILED. Not proof acceptance.
-- Statement (lines below `theorem`) is copied verbatim from inputs/Current.lean /
-- inputs/OriginalTarget.lean. Changes are body-only, see outputs/DIAGNOSIS.md R1-R5.
import Calderon.ActualReferenceExtendedCenterInverseRoom
import Calderon.ActualReferenceSmoothMultiplierSecondTaylorSmoothness
import Calderon.ActualAdjointSmoothMultiplierExtendedRoomCompatibilityTransferJointRegularity
import Calderon.SphereSobolevBalancedDualSmoothMiddle
import Calderon.CompactWithinJetBounds
-- Draft modular implementation of the exact extended-centre regularity target.
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

-- R1: same protection as every compiled sibling (Compatibility.lean:19-24); local only,
-- no data instance and no statement change.
attribute [local irreducible] referenceHighAdjointSmoothMultiplierBoundaryCommutatorFamily
  referenceSmoothMultiplierBoundaryCommutatorFamily referenceGaugeNormalHighInvertibleLocus
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  realHalfOperatorAdjointL sphereSobolevInclusionL

theorem exists_reference_adjointSmoothMultiplier_extended_center_smooth_room
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hg : IsAdmissibleMetric g)
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ∃ lam Lam d0 d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ d < d0 ∧
      (∀ p : ℝ × (R3 × ℝ), p.1 ∈ Icc (0 : ℝ) 1 →
        p.2.1 ∈ closedBall y0 (3*ρ/2) → |p.2.2| ≤ d0 →
        TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
          (fun z => a (p,z)) lam Lam ∧
        UnitBallSmallDriftData (fun z => a (p,z))
          (fun z => conformalReferenceWeightedFramedDrift g L Φ H w (p,z)) lam ∧
        p ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        p ∈ referenceGaugeNormalHighInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc) ∧
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
      ContDiffOn ℝ ∞ Gh S ∧ ContDiffOn ℝ ∞ Gn S := by
  classical
  have hρ : 0 < ρ := hData.1.2.1
  have hWitness :=
    exists_reference_commonRadius_extended_center_inverse_room
      g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  rcases hWitness with ⟨lam,Lam,d0,hlam,hd0,hd0ρ,hRoom⟩
  let d : ℝ := min 1 (d0/2)
  have hd : 0 < d := lt_min zero_lt_one (by linarith)
  have hdd0half : d ≤ d0/2 := min_le_right _ _
  have hdd0 : d ≤ d0 := hdd0half.trans (by linarith)
  have hdd0strict : d < d0 := hdd0half.trans_lt (by linarith)
  have hdρ : d ≤ ρ := hdd0.trans hd0ρ
  have hd1 : d ≤ 1 := min_le_left _ _
  refine ⟨lam,Lam,d0,d,hd,hdρ,hd1,hdd0strict,hRoom,?_⟩
  intro m hm Km hKm hmz S I J Gh GS Gn
  -- R2: no Hi/Half/Neg/Pphys/K type aliases; literal carrier types only.
  have hSegment (z : (ℝ × (R3 × ℝ)) × T) (hz : z ∈ S) (θ : ℝ)
      (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (z.1.1,(z.1.2.1,θ*z.1.2.2)) ∈
          referenceRadialEndpointInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
      (z.1.1,(z.1.2.1,θ*z.1.2.2)) ∈
          referenceGaugeNormalHighInvertibleLocus
            g L y0 Φ B ε C ρ H a w hData hcalc := by
    have hr : |z.1.2.2| ≤ d0 := (abs_le.mpr hz.1.2.2).trans hdd0
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hθr : |θ*z.1.2.2| ≤ d0 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hθabs (abs_nonneg _)).trans
        (by simpa only [one_mul] using hr)
    have h := hRoom (z.1.1,(z.1.2.1,θ*z.1.2.2)) hz.1.1 hz.1.2.1 hθr
    exact ⟨h.2.2.1,h.2.2.2⟩
  -- R3: destructure the point so it is syntactically the helper's ((q,(y,r)),t).
  have hGh : ContDiffOn ℝ ∞ Gh S := by
    rintro ⟨⟨q,y,r⟩,t⟩ hz
    exact (contDiffAt_referenceAdjointHighCommonSupportSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      m hm Km hKm hmz q y r t
      (fun θ hθ => (hSegment _ hz θ hθ).2)).contDiffWithinAt
  have hGS : ContDiffOn ℝ ∞ GS S := by
    rintro ⟨⟨q,y,r⟩,t⟩ hz
    exact (contDiffAt_referenceSmoothMultiplierCommonSupportSecondRemainder_of_segment
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      m hm Km hKm hmz q y r t
      (fun θ hθ => (hSegment _ hz θ hθ).1)).contDiffWithinAt
  -- R4: typed unapplied template for the minus adjoint; Neg diamond stays on a closed term.
  have hAdj : ContDiff ℝ ∞
      (realHalfOperatorAdjointL :
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) →
          (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))) := by
    have hTemplate := ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (F := SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) (n := ∞)
    try simp only [real_nontriviallyNormedField_normedField_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,
      clm_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq] at hTemplate
    exact hTemplate realHalfOperatorAdjointL
  have hAdjNeg : ContDiff ℝ ∞
      (fun A : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) =>
        -realHalfOperatorAdjointL A) := hAdj.neg
  have hGn : ContDiffOn ℝ ∞ Gn S := hAdjNeg.comp_contDiffOn hGS
  exact ⟨hGh,hGn⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
