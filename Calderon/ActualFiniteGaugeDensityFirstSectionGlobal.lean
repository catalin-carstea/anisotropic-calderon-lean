import Calderon.ActualFiniteGaugeDensityFirstSectionSupport
import Calderon.ActualFinitePhysicalDomainCommonRoom

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-GAUGE-DENSITY-FIRST-SECTION-GLOBAL-UPFRONT-v001.md. SAME eta, common choices before cutoff. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteGaugeDensityFirstSection
  referenceFiniteHighHorizontalSection referenceFiniteGaugeAdjointMovingBoundaryFamily
  referenceStrongDriftFamily referenceJacobiBoundaryThreeHalfCoefficientFamily
  referenceFramedNormalizedJacobian

theorem exists_reference_commonRadius_finiteGaugeDensityFirstSection_global
    (hreg : FixedDirichletRegularity) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
      ∃ G : ReferenceGaugeNormalReciprocalRoom g L Φ a
          (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)),
        ∃ E : ReferenceJacobiCompactExtensionRoom
            (referenceJacobiBoundaryThreeHalfCoefficientFamily
              g hg L y0 Φ B ε C ρ H a w hData)
            (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)),
          ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
            ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
            ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
            (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < d ∧ R y ≠ 0) →
            ∀ i : Fin 3,
              ContDiff ℝ ∞ (fun y => referenceFiniteGaugeDensityFirstSection
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i) ∧
              HasCompactSupport (fun y => referenceFiniteGaugeDensityFirstSection
                g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i) := by
  classical
  obtain ⟨lam,Lam,d,hlam,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  let Tube : Set (ℝ × (R3 × ℝ)) := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)
  have hTube : IsCompact Tube := isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)
  let G := referenceGaugeNormalReciprocalRoomOfCompact
    g L Φ y0 B ε C ρ H a w hData hg Tube hTube
  have hE : Nonempty (ReferenceJacobiCompactExtensionRoom
      (referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData) Tube) :=
    exists_referenceJacobiCompactExtensionRoom g hg L y0 Φ B ε C ρ H a w hData Tube hTube
      (fun p hp => (hRoom p hp).2.2.2.2)
  let E := Classical.choice hE
  refine ⟨d,hd,hdρ,G,E,?_⟩
  intro n q hq R hR u hu hCompact hSupportRoom i
  let η : R3 → SphereSobolev (3/2 : ℝ) := fun y => referenceFiniteGaugeDensityFirstSection
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i
  have hSupport : tsupport η ⊆ tsupport u :=
    tsupport_referenceFiniteGaugeDensityFirstSection_subset
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u i
  have hSmooth : ContDiff ℝ ∞ η := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport u
    · have hAt := hSupportRoom y hy
      have hpTube : (q,(y,R y)) ∈ Tube := by
        refine ⟨hq,?_,abs_le.mp hAt.2.1.le⟩
        simpa only [mem_closedBall,dist_eq_norm] using hAt.1.le
      have hHighRoom : (referenceStrongDriftFamily
          g L y0 Φ B ε C ρ H a w hData hcalc 1 q (y,R y)).IsInvertible :=
        (hRoom (q,(y,R y)) hpTube).2.2.2.1.1
      exact contDiffAt_referenceFiniteGaugeDensityFirstSection
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G E n q R u y i
          hu.contDiffAt hR.contDiffAt hAt.2.2 hHighRoom
    · have hyη : y ∉ tsupport η := fun h => hy (hSupport h)
      have hZero : η =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) :=
        notMem_tsupport_iff_eventuallyEq.mp hyη
      exact (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) y).congr_of_eventuallyEq hZero
  exact ⟨hSmooth,hCompact.of_isClosed_subset (isClosed_tsupport η) hSupport⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finiteGaugeDensityFirstSection_global
