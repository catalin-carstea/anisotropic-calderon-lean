import Calderon.ActualFiniteHighFullAdjointFirstSection
import Calderon.ActualFinitePhysicalDomainCommonRoom

/-! Upfront: actual-primal-moving-adjoint-domain-author-oct16-v001/
EXPANSION-actual-common-room-germ-v002.md. ACTUAL common-radius Y germ, no hNear/domain premise. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothMetricFrame MovingFrameConnection

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

attribute [local irreducible] referenceFiniteHighFullAdjointFirstSection referenceHighHorizontalAction
  referenceHighMovingBoundaryActionFamily referenceMetricGramFrame referenceFrameConnectionCoefficient
  sphereSobolevInclusionL sphereSobolevPartialSumL referenceStrongDriftFamily

include hreg

theorem exists_reference_commonRadius_fullAdjointFirstSection_graph :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ ρ ∧
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
        ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
        ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u →
        ∀ y : R3, ‖y-y0‖ < ρ → |R y| < d0 → R y ≠ 0 → ∀ i : Fin 3,
          ContDiffAt ℝ ∞ (fun z => referenceFiniteHighFullAdjointFirstSection
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u z i) y ∧
          (fun z => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
            (referenceFiniteHighFullAdjointFirstSection
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u z i)) =ᶠ[𝓝 y]
          (fun z => -referenceHighHorizontalAction g L q
              (fun x => sphereSobolevPartialSumL (3/2 : ℝ) n (u x)) z i +
            referenceHighMovingBoundaryActionFamily
              g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 R (q,z) i
                (sphereSobolevPartialSumL (3/2 : ℝ) n (u z)) -
            (∑ j : Fin 3, referenceFrameConnectionCoefficient g L q z
              (referenceMetricGramFrame g L (q,z) j) j i) •
                sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
                  (sphereSobolevPartialSumL (3/2 : ℝ) n (u z))) := by
  obtain ⟨lam,Lam,d,hlam,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_finitePhysicalDomain_room
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d/2,by positivity,(by linarith),?_⟩
  intro n q hq R hR u hu y hy hr hr0 i
  have hp : (q,(y,R y)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) := by
    refine ⟨hq,?_,abs_le.mp (show |R y| ≤ d by linarith)⟩
    simpa only [mem_closedBall,dist_eq_norm] using hy.le
  have hPoint := hRoom (q,(y,R y)) hp
  constructor
  · exact contDiffAt_referenceFiniteHighFullAdjointFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 n q R u y i
        hu.contDiffAt hR.contDiffAt hr0 hPoint.2.2.2.2 hPoint.2.2.2.1.1
  · have hNearBase : ∀ᶠ z in 𝓝 y, ‖z-y0‖ < ρ :=
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).mem_nhds hy
    have hNearRadius : ∀ᶠ z in 𝓝 y, |R z| < d :=
      (isOpen_lt (hR.continuous.abs) continuous_const).mem_nhds (show |R y| < d by linarith)
    filter_upwards [hNearBase,hNearRadius] with z hzBase hzRadius
    have hz : (q,(z,R z)) ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) := by
      refine ⟨hq,?_,abs_le.mp hzRadius.le⟩
      simpa only [mem_closedBall,dist_eq_norm] using hzBase.le
    have hzPoint := hRoom (q,(z,R z)) hz
    exact sphereSobolevInclusionL_referenceFiniteHighFullAdjointFirstSection
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg n q R u z i
        (hu.contDiffAt.differentiableAt (by simp)) lam Lam hzPoint.1 hzPoint.2.1.1

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_fullAdjointFirstSection_graph
