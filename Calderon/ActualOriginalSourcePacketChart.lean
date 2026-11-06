import Calderon.ActualNativePacketPhysicalChart
import Calderon.NativeHighDensityLocalExtension
import Calderon.ActualMixedKernelKnownSideSource
import Calderon.ActualOriginalSourcePointSourcePullback

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource ConnectionError MetricVolume MetricOperator ConformalDepth

theorem exists_actual_original_source_packet_chart
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (lam : ℝ) (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling) :
    ∃ (Fext : R3 → R3) (e : OpenPartialHomeomorph R3 R3),
      ContDiff ℝ ∞ Fext ∧
      (∀ z ∈ closedBall (0 : R3) 2, Fext =ᶠ[𝓝 z]
        (fun w => S.Xi1 (lam • packetEndpoint S L (cover.packet i) lam y r w))) ∧
      (e : R3 → R3) = Fext ∧ e.source = ball (0 : R3) 2 ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ e.target ⊆ (radiusTwoOpens : Set R3) ∧
      Fext 0 = S.Xi1 (lam • y) := by
  let P := cover.packet i
  let X : R3 → R3 := packetEndpoint S L P lam y r
  let F : R3 → R3 := fun z => S.Xi1 (lam • X z)
  have hq : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  have hq1 : lam ∈ Icc (0 : ℝ) 1 := ⟨hlam.le,hlamRoom.trans cover.dilation_le_one⟩
  have hc : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hr : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hScaled : ContDiff ℝ ∞ (fun z => lam • X z) := ContDiff.const_smul lam hX
  let V : Set R3 := (fun z => lam • X z) ⁻¹' S.coordinateRoom
  have hV : IsOpen V := S.coordinateRoom_open.preimage hScaled.continuous
  have hRoom (z : R3) (hz : z ∈ closedBall (0 : R3) 2) : lam • X z ∈ S.coordinateRoom :=
    cover.coordinate_room i lam hq y hy r hrpos hrceil z hz
  have hClosedV : closedBall (0 : R3) 2 ⊆ V := hRoom
  have hF : ContDiffOn ℝ ∞ F V :=
    S.Xi1_smooth.comp hScaled.contDiffOn (fun _ hz => hz)
  obtain ⟨Fext,hFext,_,hNear⟩ := exists_contDiff_compact_extension_eq_near_compact
    (closedBall (0 : R3) 2) V (isCompact_closedBall _ _) hV hClosedV F hF
  have hInjective : InjOn Fext (ball (0 : R3) 2) := by
    intro z hz w hw hEq
    have hz2 := ball_subset_closedBall hz
    have hw2 := ball_subset_closedBall hw
    have hFval : F z = F w :=
      (hNear z hz2).eq_of_nhds.symm.trans (hEq.trans (hNear w hw2).eq_of_nhds)
    have hScale : lam • X z = lam • X w :=
      S.Xi1_injective (hRoom z hz2) (hRoom w hw2) hFval
    have hXval : X z = X w := by
      have h := congrArg (fun v : R3 => lam⁻¹ • v) hScale
      simpa only [smul_smul,inv_mul_cancel₀ hlam.ne',one_smul] using h
    exact cover.normal_injective i lam hq y hy r hrpos hrceil hz2 hw2 hXval
  have hScaleInverse : (lam • ContinuousLinearMap.id ℝ R3).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := lam⁻¹ • ContinuousLinearMap.id ℝ R3)
    · ext v
      simp [smul_smul,hlam.ne']
    · ext v
      simp [smul_smul,hlam.ne']
  have hInvertible : ∀ z ∈ ball (0 : R3) 2, (fderiv ℝ Fext z).IsInvertible := by
    intro z hz
    have hz2 := ball_subset_closedBall hz
    rw [(hNear z hz2).fderiv_eq]
    have hXInverse : (fderiv ℝ X z).IsInvertible := by
      apply isInvertible_of_operatorMatrixMap_det_ne_zero
      have hdet := coordinateJacobianMatrix_referencePhysicalEndpoint_det_pos
        S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
        lam hq1 y hc r hr hrpos z hz2
      rw [coordinateJacobianMatrix_eq_operatorMatrixMap] at hdet
      exact hdet.ne'
    have hXiInverse : (fderiv ℝ S.Xi1 (lam • X z)).IsInvertible := by
      apply isInvertible_of_operatorMatrixMap_det_ne_zero
      have hdet := S.Xi1_jacobian (lam • X z) (hRoom z hz2)
      rw [coordinateJacobianMatrix_eq_operatorMatrixMap] at hdet
      exact hdet.ne_zero
    have hXiDiff : DifferentiableAt ℝ S.Xi1 (lam • X z) :=
      (S.Xi1_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds (hRoom z hz2))).differentiableAt (by simp)
    have hSX : HasFDerivAt (fun w => lam • X w)
        ((lam • ContinuousLinearMap.id ℝ R3).comp (fderiv ℝ X z)) z := by
      rw [ContinuousLinearMap.smul_comp,ContinuousLinearMap.id_comp]
      exact (hX.differentiable (by simp) z).hasFDerivAt.const_smul lam
    have hDF : fderiv ℝ F z = (fderiv ℝ S.Xi1 (lam • X z)).comp
        ((lam • ContinuousLinearMap.id ℝ R3).comp (fderiv ℝ X z)) :=
      (hXiDiff.hasFDerivAt.comp z hSX).fderiv
    rw [hDF]
    exact hXiInverse.comp (hScaleInverse.comp hXInverse)
  obtain ⟨e,he,hs,ht,hInverse,_⟩ :=
    exists_fixed_physical_chart_of_injOn_isInvertible Fext hFext hInjective hInvertible
  have hTarget : e.target ⊆ (radiusTwoOpens : Set R3) := by
    rw [ht]
    rintro x ⟨z,hz,rfl⟩
    rw [(hNear z (ball_subset_closedBall hz)).eq_of_nhds]
    exact S.Xi1_room (lam • X z) (hRoom z (ball_subset_closedBall hz))
  have hCenter : Fext 0 = S.Xi1 (lam • y) := by
    calc
      Fext 0 = F 0 := (hNear 0 (by norm_num)).eq_of_nhds
      _ = S.Xi1 (lam • y) := by
        dsimp only [F,X]
        rw [packetEndpoint_zero_eq_center S L P lam hq1 y hy r]
  exact ⟨Fext,e,hFext,hNear,he,hs,hInverse,hTarget,hCenter⟩

theorem exists_actual_original_source_packet_chart_with_jacobian
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (lam : ℝ) (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling) :
    ∃ (Fext : R3 → R3) (e : OpenPartialHomeomorph R3 R3),
      ContDiff ℝ ∞ Fext ∧
      (∀ z ∈ closedBall (0 : R3) 2, Fext =ᶠ[𝓝 z]
        (fun w => S.Xi1 (lam • packetEndpoint S L (cover.packet i) lam y r w))) ∧
      (e : R3 → R3) = Fext ∧ e.source = ball (0 : R3) 2 ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ e.target ⊆ (radiusTwoOpens : Set R3) ∧
      Fext 0 = S.Xi1 (lam • y) ∧
      ∀ z ∈ ball (0 : R3) 2, IsUnit (coordinateJacobianMatrix Fext z).det := by
  obtain ⟨F,e,hF,hNear,he,hs,hInverse,hTarget,hCenter⟩ :=
    exists_actual_original_source_packet_chart S L cover i lam hlam hlamRoom y hy r hrpos hrceil
  refine ⟨F,e,hF,hNear,he,hs,hInverse,hTarget,hCenter,?_⟩
  intro z hz
  exact coordinateJacobianMatrix_isUnit_of_smooth_open_chart F hF e he hInverse z (by rwa [hs])

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
