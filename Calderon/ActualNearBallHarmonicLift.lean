import Calderon.LocalSmoothAmbientExtension
import Calderon.ActualPhysicalHarmonicCovariance
/-! Source-only author original near-ball datum bridge. Genuine local
extension and exact actual harmonic/value/radial correspondence were sealed
first. No global smooth premise is substituted into the manuscript target,
and no full moving-family/Psi closure or acceptance is claimed. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Gradient InnerProductSpace Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator

theorem coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
    (g : MatrixField) (u v : R3 → ℝ) (x : R3) (h : u =ᶠ[𝓝 x] v) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x =
      coordinateFluxDivergence (metricDivergenceFlux g v) x := by
  have hFD : fderiv ℝ u =ᶠ[𝓝 x] fderiv ℝ v := h.fderiv
  have hGrad : gradient u =ᶠ[𝓝 x] gradient v := by
    filter_upwards [hFD] with y hy
    apply ext_inner_right ℝ
    intro W
    rw [inner_gradient_left,inner_gradient_left,hy]
  have hFlux : metricDivergenceFlux g u =ᶠ[𝓝 x] metricDivergenceFlux g v :=
    hGrad.mono (fun y hy => congrArg (matrixOperatorMap (principalCoefficient g y)) hy)
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y => metricDivergenceFlux g u y i) =ᶠ[𝓝 x]
      (fun y => metricDivergenceFlux g v y i) :=
    hFlux.mono (fun y hy => congrArg (fun V : R3 => V i) hy)
  exact congrArg (fun F : R3 →L[ℝ] ℝ =>
    F (OAI.AnisotropicCalderon.NormalCoordinatesFrame.coordinateVector i)) hi.fderiv_eq

end OAI.AnisotropicCalderon.ConnectionError

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume MetricOperator ConnectionError SphereHarmonic

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hg hData

theorem exists_referenceHarmonicLift_of_near_ball_harmonic
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (s : ℕ)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hr0 : r ≠ 0)
    (hi : (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)).IsInvertible)
    (S : Set R3) (hS : IsOpen S) (u : R3 → ℝ) (hu : ContDiffOn ℝ ∞ u S)
    (hCover : (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) ''
      closedBall (0 : R3) 1 ⊆ S)
    (hphysical : ∀ x ∈ S,
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) u) x = 0) :
    ∃ v : SmoothData,
      (∀ x ∈ (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) ''
        closedBall (0 : R3) 1, v.1 =ᶠ[𝓝 x] u) ∧
      (referenceHarmonicLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc s q (y,r)
        (smoothBallSobolev (s+2)
          (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v)) =
        smoothBallSobolev (s+2)
          (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v)) ∧
      (∀ «ω» : UnitSphere,
        smoothSphereValue (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v) «ω» =
          u (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),«ω».val)))) ∧
      (∀ «ω» : UnitSphere,
        smoothRadialSphere (referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r v) «ω» =
          fderiv ℝ u (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),«ω».val)))
            (r • referenceFramedNormalizedJacobian g L Φ (q,((y,r),«ω».val)) «ω».val)) := by
  let X : R3 → R3 := fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))
  let K := X '' closedBall (0 : R3) 1
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_const.prodMk ((contDiff_const.prodMk contDiff_const).prodMk contDiff_id))
  have hK : IsCompact K := (isCompact_closedBall (0 : R3) 1).image hX.continuous
  obtain ⟨v,_,hNear⟩ := exists_smoothData_eq_near_compact K S hK hS hCover u hu
  have hPhysicalV : ∀ z ∈ (ballOpens : Set R3),
      coordinateFluxDivergence (metricDivergenceFlux (fun x => g (q • x)) v.1) (X z) = 0 := by
    intro z hz
    have hPoint : X z ∈ K := ⟨z,ball_subset_closedBall hz,rfl⟩
    exact (coordinateFluxDivergence_metricDivergenceFlux_congr_of_eventuallyEq
      (fun x => g (q • x)) v.1 u (X z) (hNear (X z) hPoint)).trans
        (hphysical (X z) (hCover hPoint))
  have hLift := referenceHarmonicLiftFamily_physical_harmonic_eq_self
    g hg L y0 Φ B ε C ρ H a w hData hcalc hreg s q hq y hy r hr hr0 v hi hPhysicalV
  have hSphereK («ω» : UnitSphere) : X «ω».val ∈ K := by
    have hn : ‖«ω».val‖ = 1 := by
      simpa [UnitSphere,Metric.sphere,dist_eq_norm] using «ω».property
    have hClosed : «ω».val ∈ closedBall (0 : R3) 1 := by
      change dist «ω».val (0 : R3) ≤ 1
      rw [dist_zero_right,hn]
    exact ⟨«ω».val,hClosed,rfl⟩
  refine ⟨v,hNear,hLift,?_,?_⟩
  · intro «ω»
    change v.1 (X «ω».val) = u (X «ω».val)
    exact (hNear (X «ω».val) (hSphereK «ω»)).self_of_nhds
  · intro «ω»
    rw [smoothRadialSphere_referencePhysicalPullback_apply
      g hg L y0 Φ B hData.1.1.1 q y r v «ω»]
    rw [(hNear (X «ω».val) (hSphereK «ω»)).fderiv_eq]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
