import Calderon.LocalSmoothFamilyExtension
import Calderon.ActualNearBallHarmonicLift
/-! Actual moving-neighborhood physical/native harmonic bridge.
One ambient extension, actual varying datum, and exact physical traces. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume MetricOperator ConnectionError SphereHarmonic

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hg hData

theorem exists_referenceHarmonicLift_family_of_near_ball_harmonic
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ < 4*ρ)
    (r : ℝ) (hr : |r| < 4*ρ) (hr0 : r ≠ 0)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)).IsInvertible)
    (S : Set R3) (hS : IsOpen S) (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S)
    (hCover : (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) ''
      closedBall (0 : R3) 1 ⊆ S)
    (hphysical : ∀ x ∈ S,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u) x = 0) :
    ∃ (v : SmoothData) (U : Set (R3 × ℝ)),
      HasCompactSupport v.1 ∧ IsOpen U ∧ (y,r) ∈ U ∧
      ∀ p ∈ U,
        ‖p.1-y0‖ < 4*ρ ∧ |p.2| < 4*ρ ∧ p.2 ≠ 0 ∧
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p).IsInvertible ∧
        (fun z => referenceFramedPhysicalEndpoint g L Φ (q,(p,z))) ''
          closedBall (0 : R3) 1 ⊆ S ∧
        (∀ z ∈ closedBall (0 : R3) 1,
          v.1 =ᶠ[𝓝 (referenceFramedPhysicalEndpoint g L Φ (q,(p,z)))] u) ∧
        (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q p
          (smoothBallSobolev (s+2)
            (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q p.1 p.2 v)) =
          smoothBallSobolev (s+2)
            (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q p.1 p.2 v)) ∧
        (∀ «ω» : UnitSphere,
          smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q p.1 p.2 v) «ω» =
            u (referenceFramedPhysicalEndpoint g L Φ (q,(p,«ω».val)))) ∧
        (∀ «ω» : UnitSphere,
          smoothRadialSphere (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q p.1 p.2 v) «ω» =
            fderiv ℝ u (referenceFramedPhysicalEndpoint g L Φ (q,(p,«ω».val)))
              (p.2 • referenceFramedNormalizedJacobian g L Φ (q,(p,«ω».val)) «ω».val)) := by
  letI : CompleteSpace (StrongDirichletSpace s) := instCompleteSpaceStrongDirichletSpace s
  let X : (R3 × ℝ) × R3 → R3 := fun pz =>
    referenceFramedPhysicalEndpoint g L Φ (q,pz)
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_const.prodMk contDiff_id)
  obtain ⟨v,U0,hv,hU0,hBaseU0,hFamily⟩ :=
    exists_smoothData_eq_near_compact_family X hX.continuous (y,r)
      (closedBall (0 : R3) 1) S (isCompact_closedBall _ _) hS hCover u hu
  let A := referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q
  have hA : ContDiff ℝ ∞ A :=
    (contDiff_referenceOrdinaryStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q).clm_comp
      contDiff_const
  let Q : Set (R3 × ℝ) := {p | ‖p.1-y0‖ < 4*ρ ∧ |p.2| < 4*ρ ∧ p.2 ≠ 0 ∧ (A p).IsInvertible}
  have hQ : IsOpen Q := by
    have hY : IsOpen {p : R3 × ℝ | ‖p.1-y0‖ < 4*ρ} :=
      isOpen_lt (continuous_fst.sub continuous_const).norm continuous_const
    have hR : IsOpen {p : R3 × ℝ | |p.2| < 4*ρ} :=
      isOpen_lt continuous_snd.abs continuous_const
    have hNZ : IsOpen {p : R3 × ℝ | p.2 ≠ 0} :=
      isClosed_singleton.isOpen_compl.preimage continuous_snd
    have hI : IsOpen {p : R3 × ℝ | (A p).IsInvertible} :=
      ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hA.continuous
    exact hY.inter (hR.inter (hNZ.inter hI))
  have hBaseQ : (y,r) ∈ Q := ⟨hy,hr,hr0,hi⟩
  refine ⟨v,U0 ∩ Q,hv,hU0.inter hQ,⟨hBaseU0,hBaseQ⟩,?_⟩
  intro p hp
  obtain ⟨hCoverP,hNearP⟩ := hFamily p hp.1
  obtain ⟨hY,hR,hNZ,hI⟩ := hp.2
  have hPhysicalV : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) v.1) (X (p,z)) = 0 := by
    intro z hz
    have hClosed : z ∈ closedBall (0 : R3) 1 := ball_subset_closedBall hz
    exact (coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
      (fun x => g (q • x)) v.1 u (X (p,z)) (hNearP z hClosed)).trans
        (hphysical (X (p,z)) (hCoverP ⟨z,hClosed,rfl⟩))
  have hLift := referenceHarmonicLiftFamily_physical_harmonic_eq_self
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg s q hq p.1 hY.le p.2 hR.le hNZ v hI hPhysicalV
  have hSphereClosed («ω» : UnitSphere) : «ω».val ∈ closedBall (0 : R3) 1 := by
    have hn : ‖«ω».val‖ = 1 := by
      simpa [UnitSphere,Metric.sphere,dist_eq_norm] using «ω».property
    change dist «ω».val (0 : R3) ≤ 1
    rw [dist_zero_right,hn]
  refine ⟨hY,hR,hNZ,hI,hCoverP,hNearP,hLift,?_,?_⟩
  · intro «ω»
    change v.1 (X (p,«ω».val)) = u (X (p,«ω».val))
    exact (hNearP «ω».val (hSphereClosed «ω»)).self_of_nhds
  · intro «ω»
    rw [smoothRadialSphere_referencePhysicalPullback_apply
      g hg L y0 Φ B hData.1.1.1 q p.1 p.2 v «ω»]
    rw [(hNearP «ω».val (hSphereClosed «ω»)).fderiv_eq]


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
