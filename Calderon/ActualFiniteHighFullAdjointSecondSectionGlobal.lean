import Calderon.ActualFullAdjointFirstActionRegularity
import Calderon.ActualFiniteHighFullAdjointFirstSectionGlobal
import Calderon.ActualFinitePhysicalDomainCommonRoom

/-! Full AUTHOR upfront: actual-Y-second-action-domain-author-oct16-v001/
EXPANSION-global-uncompressed-second-section-v010.md. Literal second Y section,
no smooth choice of the pointwise existential domain witness. -/
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

attribute [local irreducible] referenceFiniteHighFullAdjointFirstSection
  referenceHighFullAdjointFirstAction referenceMetricGramFrame referenceStrongDriftFamily

lemma exists_reference_commonRadius_fullAdjointSecondSection_global
    (hreg : FixedDirichletRegularity) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ ρ ∧
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d0 ∧ R y ≠ 0) →
      ∀ i j : Fin 3,
        let eta : R3 → SphereSobolev (3/2 : ℝ) := fun y => referenceFiniteHighFullAdjointFirstSection
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i
        let xi : R3 → SphereSobolev (1/2 : ℝ) := fun y => referenceHighFullAdjointFirstAction
          g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R eta y j
        ContDiff ℝ ∞ xi ∧ HasCompactSupport xi := by
  obtain ⟨dY,hdY,hdYρ,hGlobal⟩ := exists_reference_commonRadius_fullAdjointFirstSection_global
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  obtain ⟨lam,Lam,d,hlam,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨min dY (d/2),lt_min hdY (show 0 < d/2 by positivity),
    (min_le_left _ _).trans hdYρ,?_⟩
  intro n q hq R hR u hu hCompact hSupportRoom i j
  let eta : R3 → SphereSobolev (3/2 : ℝ) := fun y => referenceFiniteHighFullAdjointFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i
  let xi : R3 → SphereSobolev (1/2 : ℝ) := fun y => referenceHighFullAdjointFirstAction
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R eta y j
  have hSupportY : ∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < dY ∧ R y ≠ 0 := by
    intro y hy
    have hs := hSupportRoom y hy
    exact ⟨hs.1,hs.2.1.trans_le (min_le_left _ _),hs.2.2⟩
  have hEta : ContDiff ℝ ∞ eta ∧ HasCompactSupport eta :=
    hGlobal n q hq R hR u hu hCompact hSupportY i
  have hEtaSupport : tsupport eta ⊆ tsupport u :=
    tsupport_referenceFiniteHighFullAdjointFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u i
  have hXiSupport : tsupport xi ⊆ tsupport eta :=
    tsupport_referenceHighFullAdjointFirstAction_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R eta j
  have hSmooth : ContDiff ℝ ∞ xi := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport eta
    · have hs := hSupportRoom y (hEtaSupport hy)
      have hrHalf : |R y| < d/2 := hs.2.1.trans_le (min_le_right _ _)
      have hrD : |R y| ≤ d := by linarith only [hrHalf,hd]
      have hp : (q,(y,R y)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) := by
        refine ⟨hq,?_,abs_le.mp hrD⟩
        simpa only [mem_closedBall,dist_eq_norm] using hs.1.le
      have ha := hRoom (q,(y,R y)) hp
      exact contDiffAt_referenceHighFullAdjointFirstAction
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 q R eta y j
          hEta.1.contDiffAt hR.contDiffAt hs.2.2 ha.2.2.2.2 ha.2.2.2.1.2
    · have hZero : xi =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (hXiSupport h))
      exact (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : R3 => (0 : SphereSobolev (1/2 : ℝ))) y).congr_of_eventuallyEq hZero
  exact ⟨hSmooth,hEta.2.of_isClosed_subset (isClosed_tsupport xi) hXiSupport⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_fullAdjointSecondSection_global
