import Calderon.ActualFiniteHighFullAdjointFirstSectionSupport
import Calderon.ActualFiniteHighFullAdjointFirstSectionRoom

/-! Full AUTHOR upfront: actual-primal-moving-adjoint-domain-author-oct16-v001/
EXPANSION-same-section-support-global-v008.md. SAME explicit uncompressed Y section. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHighPrimalMovingBoundaryFamily
  referenceFiniteHighHorizontalSection referenceFiniteHighFullAdjointFirstSection
  sphereSobolevPartialSumL referenceMetricGramFrame referenceFrameConnectionCoefficient

theorem exists_reference_commonRadius_fullAdjointFirstSection_global
    (hreg : FixedDirichletRegularity) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ ρ ∧
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
        ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
        ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
        (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) →
        ∀ i : Fin 3,
          ContDiff ℝ ∞ (fun y => referenceFiniteHighFullAdjointFirstSection
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i) ∧
          HasCompactSupport (fun y => referenceFiniteHighFullAdjointFirstSection
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i) := by
  classical
  obtain ⟨d0,hd0,hdρ,hLocal⟩ := exists_reference_commonRadius_fullAdjointFirstSection_graph
    g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0
  refine ⟨d0,hd0,hdρ,?_⟩
  intro n q hq R hR u hu hCompact hSupportRoom i
  let η : R3 → SphereSobolev (3/2 : ℝ) := fun y => referenceFiniteHighFullAdjointFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i
  have hSupport : tsupport η ⊆ tsupport u :=
    tsupport_referenceFiniteHighFullAdjointFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u i
  have hSmooth : ContDiff ℝ ∞ η := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport u
    · have hAt := hSupportRoom y hy
      exact (hLocal n q hq R hR u hu y hAt.1 hAt.2.1 hAt.2.2 i).1
    · have hyη : y ∉ tsupport η := fun h => hy (hSupport h)
      have hZero : η =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) :=
        notMem_tsupport_iff_eventuallyEq.mp hyη
      exact (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) y).congr_of_eventuallyEq hZero
  exact ⟨hSmooth,hCompact.of_isClosed_subset (isClosed_tsupport η) hSupport⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_fullAdjointFirstSection_global
