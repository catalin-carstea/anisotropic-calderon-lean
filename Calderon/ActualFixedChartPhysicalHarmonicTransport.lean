import Calderon.ActualNativePacketPhysicalChart
import Calderon.NativeHighDensityLocalExtension
import Calderon.ActualFiberRawFluxGauge
import Calderon.ActualDoubleBallPhysicalHarmonicEquivalence

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Gradient InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricVolume MetricOperator

private theorem coordinateFluxDivergence_matrixGradient_congr_of_eventuallyEq
    (A : MatrixField) (u v : R3 → ℝ) (x : R3) (h : u =ᶠ[𝓝 x] v) :
    coordinateFluxDivergence (fun y => matrixOperatorMap (A y) (gradient u y : R3)) x =
      coordinateFluxDivergence (fun y => matrixOperatorMap (A y) (gradient v y : R3)) x := by
  have hFlux : (fun y => matrixOperatorMap (A y) (gradient u y : R3)) =ᶠ[𝓝 x]
      (fun y => matrixOperatorMap (A y) (gradient v y : R3)) :=
    h.gradient.mono (fun y hy => congrArg (matrixOperatorMap (A y)) hy)
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun y => (matrixOperatorMap (A y) (gradient u y : R3)) i) =ᶠ[𝓝 x]
      (fun y => (matrixOperatorMap (A y) (gradient v y : R3)) i) :=
    hFlux.mono (fun y hy => congrArg (fun V : R3 => V i) hy)
  exact congrArg (fun D : R3 →L[ℝ] ℝ => D (NormalCoordinatesFrame.coordinateVector i)) hi.fderiv_eq

end OAI.AnisotropicCalderon.ConnectionError

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume MetricOperator ConnectionError MixedKernelConstructionTask

variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hg hData in
theorem exists_fixed_chart_physical_harmonic_neighborhood_of_normalized
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (y : R3) (hy : ‖y-y0‖ ≤ 4*ρ)
    (r : ℝ) (hr : |r| ≤ 4*ρ) (hrpos : 0 < r)
    (e : OpenPartialHomeomorph R3 R3)
    (he : (e : R3 → R3) = fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z)))
    (hs : e.source = ball (0 : R3) 2) (hSmooth : ContDiffOn ℝ ∞ e.symm e.target)
    (v : SmoothData) (O : Set R3) (hO : IsOpen O)
    (hKO : closedBall (0 : R3) 1 ⊆ O) (hODouble : O ⊆ ball (0 : R3) 2)
    (hPDE : ∀ z ∈ O, coordinateFluxDivergence (fun x => matrixOperatorMap
      (referencePhysicalNormalizedPrincipalCoefficient g L Φ H (q,(y,r)) x)
      (gradient v.1 x : R3)) z = 0) :
    ∃ u : SmoothData, ∃ V : Set R3, HasCompactSupport u.1 ∧ IsOpen V ∧
      (fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))) '' closedBall (0 : R3) 1 ⊆ V ∧
      (∀ x ∈ V, coordinateFluxDivergence
        (metricDivergenceFlux (fun x => g (q • x)) u.1) x = 0) ∧
      ∀ z ∈ closedBall (0 : R3) 1,
        (fun t => u.1 (referenceFramedPhysicalEndpoint g L Φ (q,((y,r),t)))) =ᶠ[𝓝 z] v.1 := by
  let X : R3 → R3 := fun z => referenceFramedPhysicalEndpoint g L Φ (q,((y,r),z))
  have hTheta : ContDiff ℝ ∞ (fun t : ℝ × (R3 × R3) => (Φ t.1 t.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint g hg L Φ hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hLeft (z : R3) (hz : z ∈ ball (0 : R3) 2) : e.symm (X z) = z := by
    have hzs : z ∈ e.source := by rwa [hs]
    simpa only [he] using e.left_inv hzs
  have hMap (z : R3) (hz : z ∈ ball (0 : R3) 2) : X z ∈ e.target := by
    have hzs : z ∈ e.source := by rwa [hs]
    simpa only [he] using e.map_source hzs
  have hCompact : IsCompact (X '' closedBall (0 : R3) 1) :=
    (isCompact_closedBall _ _).image hX.continuous
  have hInside : X '' closedBall (0 : R3) 1 ⊆ e.target := by
    rintro x ⟨z,hz,rfl⟩
    exact hMap z (closedBall_subset_ball (by norm_num) hz)
  have hPhysicalSmooth : ContDiffOn ℝ ∞ (fun x => v.1 (e.symm x)) e.target :=
    v.2.comp_contDiffOn hSmooth
  obtain ⟨uRaw,huSmooth,huCompact,huGerm⟩ := exists_contDiff_compact_extension_eq_near_compact
    (X '' closedBall (0 : R3) 1) e.target hCompact e.open_target hInside
    (fun x => v.1 (e.symm x)) hPhysicalSmooth
  let u : SmoothData := ⟨uRaw,huSmooth⟩
  have hNear : ∀ z ∈ closedBall (0 : R3) 1,
      (fun t => u.1 (X t)) =ᶠ[𝓝 z] v.1 := by
    intro z hz
    have hG := (huGerm (X z) ⟨z,hz,rfl⟩).comp_tendsto (hX.continuous.tendsto z)
    have hLocalInv : (fun t => v.1 (e.symm (X t))) =ᶠ[𝓝 z] v.1 := by
      have hz2 : z ∈ ball (0 : R3) 2 := closedBall_subset_ball (by norm_num) hz
      filter_upwards [isOpen_ball.mem_nhds hz2] with t ht
      rw [hLeft t ht]
    exact hG.trans hLocalInv
  let b : SmoothData := referencePhysicalPullbackData g hg L y0 Φ B hData.1.1.1 q y r u
  let G : Set R3 := {z | b.1 =ᶠ[𝓝 z] v.1}
  let N : Set R3 := O ∩ G
  have hGOpen : IsOpen G := isOpen_setOfPred_eventually_nhds
  have hNOpen : IsOpen N := hO.inter hGOpen
  have hKN : closedBall (0 : R3) 1 ⊆ N := fun z hz => ⟨hKO hz,hNear z hz⟩
  have hNDouble : N ⊆ ball (0 : R3) 2 := fun _ hz => hODouble hz.1
  let V : Set R3 := e.target ∩ e.symm ⁻¹' N
  have hVOpen : IsOpen V := hSmooth.continuousOn.isOpen_inter_preimage e.open_target hNOpen
  have hCover : X '' closedBall (0 : R3) 1 ⊆ V := by
    rintro x ⟨z,hz,rfl⟩
    have hz2 : z ∈ ball (0 : R3) 2 := closedBall_subset_ball (by norm_num) hz
    refine ⟨hMap z hz2,?_⟩
    change e.symm (X z) ∈ N
    rw [hLeft z hz2]
    exact hKN hz
  refine ⟨u,V,huCompact,hVOpen,hCover,?_,hNear⟩
  intro x hx
  have hzN : e.symm x ∈ N := hx.2
  have hzDouble : e.symm x ∈ ball (0 : R3) 2 := hNDouble hzN
  have hRaw : coordinateFluxDivergence (fun t => matrixOperatorMap
      (referencePhysicalNormalizedPrincipalCoefficient g L Φ H (q,(y,r)) t)
      (gradient b.1 t : R3)) (e.symm x) = 0 :=
    (coordinateFluxDivergence_matrixGradient_congr_of_eventuallyEq
      (referencePhysicalNormalizedPrincipalCoefficient g L Φ H (q,(y,r)))
      b.1 v.1 (e.symm x) hzN.2).trans (hPDE (e.symm x) hzN.1)
  have hPositive : referenceRescaledPositiveExpression g L Φ H w (q,(y,r)) b.1 (e.symm x) = 0 :=
    (coordinateFluxDivergence_referenceNormalizedCoefficient_zero_iff
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr (e.symm x)
      (ball_subset_closedBall hzDouble) b).mp hRaw
  have hPhysical : coordinateFluxDivergence
      (metricDivergenceFlux (fun t => g (q • t)) u.1) (X (e.symm x)) = 0 :=
    (referenceRescaledPositiveExpression_physical_pullback_zero_iff_on_doubleBall
      g hg L y0 Φ B ε C ρ H a w hData q hq y hy r hr hrpos.ne' u (e.symm x) hzDouble).mp hPositive
  have hRight : X (e.symm x) = x := by
    have h := e.right_inv hx.1
    simpa only [he] using h
  rw [hRight] at hPhysical
  exact hPhysical

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge MetricVolume MetricOperator ConnectionError DirichletFamily.DriftBootstrap

theorem exists_actual_packet_physical_harmonic_neighborhood_of_normalized
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling)
    (v : SmoothData) (O : Set R3) (hO : IsOpen O)
    (hKO : closedBall (0 : R3) 1 ⊆ O) (hODouble : O ⊆ ball (0 : R3) 2)
    (hPDE : ∀ z ∈ O, coordinateFluxDivergence (fun x => matrixOperatorMap
      (referencePhysicalNormalizedPrincipalCoefficient S.g1 L (cover.packet i).Phi
        (cover.packet i).H (q,(y,r)) x) (gradient v.1 x : R3)) z = 0) :
    ∃ u : SmoothData, ∃ V : Set R3, HasCompactSupport u.1 ∧ IsOpen V ∧
      packetEndpoint S L (cover.packet i) q y r '' closedBall (0 : R3) 1 ⊆ V ∧
      (∀ x ∈ V, coordinateFluxDivergence
        (metricDivergenceFlux (fun x => S.g1 (q • x)) u.1) x = 0) ∧
      ∀ z ∈ closedBall (0 : R3) 1,
        (fun t => u.1 (packetEndpoint S L (cover.packet i) q y r t)) =ᶠ[𝓝 z] v.1 := by
  let P := cover.packet i
  obtain ⟨e,he,hs,_,hSmooth,_⟩ := exists_actual_native_packet_physical_chart
    S L cover i q hq y hy r hrpos hrceil
  have hq1 : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1,hq.2.trans cover.dilation_le_one⟩
  have hc : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hr : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  exact exists_fixed_chart_physical_harmonic_neighborhood_of_normalized
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
    q hq1 y hc r hr hrpos e he hs hSmooth v O hO hKO hODouble hPDE

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
