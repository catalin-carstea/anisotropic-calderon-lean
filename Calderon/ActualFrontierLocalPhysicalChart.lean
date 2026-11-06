import Calderon.ActualFrontierAllSourceLocalContinuation
import Calderon.ActualNativePacketPhysicalChart
import Calderon.MetricPullbackComposition
import Calderon.ActualSourceOpenMatchCovectorGram

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions Matrix.Norms.Elementwise Matrix
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource MetricOperator MetricVolume ConnectionError

/-- A coordinate contact ball with equality of its two carrier metrics and
every original source response yields an actual local physical isometry. -/
theorem exists_local_physical_match_of_ball_all_source_agreement
    (S : KnownSideSourceData) (r : ℝ) (hr : 0 < r)
    (hRoom : ball (0 : R3) r ⊆ S.coordinateRoom)
    (hMetric : EqOn S.g1 S.g2 (ball (0 : R3) r))
    (hAll : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      EqOn (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible s (S.Xi1 z))
        (fun z => radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
          S.original2_admissible s (S.Xi2 z)) (ball (0 : R3) r)) :
    ∃ (Z : Set R3) (Phi : R3 → R3),
      Z = S.Xi2 '' ball (0 : R3) r ∧
      IsOpen Z ∧ IsConnected Z ∧ S.Xi2 0 ∈ Z ∧
      Z ⊆ (radiusTwoOpens : Set R3) ∧
      ContDiffOn ℝ ∞ Phi Z ∧ Set.InjOn Phi Z ∧
      (∀ x ∈ Z, Phi x ∈ (radiusTwoOpens : Set R3)) ∧
      (∀ x ∈ Z, IsUnit (coordinateJacobianMatrix Phi x).det) ∧
      EqOn (pullbackMetric S.original1 Phi) S.original2 Z ∧
      (∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ Z,
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
          S.original1_admissible s (Phi x) =
        radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
          S.original2_admissible s x) ∧
      (∀ z ∈ ball (0 : R3) r, Phi (S.Xi2 z) = S.Xi1 z) := by
  let B : Set R3 := ball (0 : R3) r
  have hB : IsOpen B := isOpen_ball
  have hSmooth2 : ContDiffOn ℝ ∞ S.Xi2 B := S.Xi2_smooth.mono hRoom
  have hInj2 : Set.InjOn S.Xi2 B := S.Xi2_injective.mono hRoom
  have hInv2 : ∀ z ∈ B, (fderiv ℝ S.Xi2 z).IsInvertible := by
    intro z hz
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    rw [← coordinateJacobianMatrix_eq_operatorMatrixMap]
    exact isUnit_iff_ne_zero.mp (S.Xi2_jacobian z (hRoom hz))
  have hOpen2 : IsOpenMap (B.domRestrict S.Xi2) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    obtain ⟨D,hD⟩ := hInv2 z z.property
    have hDz : HasFDerivAt S.Xi2 (D : R3 →L[ℝ] R3) (z : R3) := by
      rw [hD]
      exact (hSmooth2.contDiffAt (hB.mem_nhds z.property)).differentiableAt
        (by simp) |>.hasFDerivAt
    have hm : Filter.map S.Xi2 (𝓝 (z : R3)) = 𝓝 (S.Xi2 (z : R3)) :=
      ((hSmooth2.contDiffAt (hB.mem_nhds z.property)).hasStrictFDerivAt'
        hDz (by simp)).map_nhds_eq_of_equiv
    have hs : Filter.map ((↑) : B → R3) (𝓝 z) = 𝓝 (z : R3) :=
      map_nhds_subtype_coe_eq_nhds z.property (hB.mem_nhds z.property)
    change 𝓝 (S.Xi2 (z : R3)) ≤ Filter.map (S.Xi2 ∘ ((↑) : B → R3)) (𝓝 z)
    rw [← Filter.map_map, hs, hm]
  let pe : PartialEquiv R3 R3 := hInj2.toPartialEquiv S.Xi2 B
  let e : OpenPartialHomeomorph R3 R3 :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict pe hSmooth2.continuousOn hOpen2 hB
  have he : (e : R3 → R3) = S.Xi2 := rfl
  have hSource : e.source = B := rfl
  have hTarget : e.target = S.Xi2 '' B := rfl
  have hInvSmooth : ContDiffOn ℝ ∞ e.symm e.target := by
    intro x hx
    have hz : e.symm x ∈ B := by simpa only [hSource] using e.map_target hx
    obtain ⟨D,hD⟩ := hInv2 (e.symm x) hz
    have hd : HasFDerivAt e (D : R3 →L[ℝ] R3) (e.symm x) := by
      change HasFDerivAt S.Xi2 (D : R3 →L[ℝ] R3) (e.symm x)
      rw [hD]
      exact (hSmooth2.contDiffAt (hB.mem_nhds hz)).differentiableAt
        (by simp) |>.hasFDerivAt
    exact (e.contDiffAt_symm hx hd (hSmooth2.contDiffAt (hB.mem_nhds hz))).contDiffWithinAt
  let Z : Set R3 := e.target
  let Phi : R3 → R3 := S.Xi1 ∘ e.symm
  have hInvRoom : ∀ x ∈ Z, e.symm x ∈ B := by
    intro x hx
    simpa only [Z, hSource] using e.map_target hx
  have hPhiChart : ∀ z ∈ B, Phi (S.Xi2 z) = S.Xi1 z := by
    intro z hz
    change S.Xi1 (e.symm (e z)) = S.Xi1 z
    rw [e.left_inv (show z ∈ e.source by simpa only [hSource] using hz)]
  have hZopen : IsOpen Z := e.open_target
  have hZconn : IsConnected Z := by
    rw [show Z = S.Xi2 '' B from hTarget]
    exact ((convex_ball (0 : R3) r).isConnected ⟨0, mem_ball_self hr⟩).image
      S.Xi2 hSmooth2.continuousOn
  have hZrange : Z ⊆ (radiusTwoOpens : Set R3) := by
    intro x hx
    have hz := hInvRoom x hx
    have hRight : e (e.symm x) = x := e.right_inv hx
    rw [he] at hRight
    rw [← hRight]
    exact S.Xi2_room (e.symm x) (hRoom hz)
  have hPhiSmooth : ContDiffOn ℝ ∞ Phi Z := by
    exact (S.Xi1_smooth.mono hRoom).comp hInvSmooth hInvRoom
  have hPhiInj : Set.InjOn Phi Z := by
    intro x hx y hy hxy
    have hEq : e.symm x = e.symm y :=
      S.Xi1_injective (hRoom (hInvRoom x hx)) (hRoom (hInvRoom y hy)) hxy
    calc
      x = e (e.symm x) := (e.right_inv hx).symm
      _ = e (e.symm y) := by rw [hEq]
      _ = y := e.right_inv hy
  have hPhiRange : ∀ x ∈ Z, Phi x ∈ (radiusTwoOpens : Set R3) := by
    intro x hx
    exact S.Xi1_room (e.symm x) (hRoom (hInvRoom x hx))
  have hPhiDiff : ∀ x ∈ Z, DifferentiableAt ℝ Phi x := by
    intro x hx
    exact (hPhiSmooth.contDiffAt (hZopen.mem_nhds hx)).differentiableAt (by simp)
  have hE2Diff : ∀ z ∈ B, DifferentiableAt ℝ S.Xi2 z := by
    intro z hz
    exact (hSmooth2.contDiffAt (hB.mem_nhds hz)).differentiableAt (by simp)
  have hMetricPhysical : EqOn (pullbackMetric S.original1 Phi) S.original2 Z := by
    intro x hx
    let z := e.symm x
    have hz : z ∈ B := hInvRoom x hx
    have hxz : S.Xi2 z = x := by simpa only [he] using e.right_inv hx
    have hComp : pullbackMetric S.original1 (Phi ∘ S.Xi2) z =
        pullbackMetric (pullbackMetric S.original1 Phi) S.Xi2 z :=
      pullbackMetric_comp_of_differentiableAt S.original1 Phi S.Xi2 z
        (by rw [hxz]; exact hPhiDiff x hx) (hE2Diff z hz)
    have hNear : Phi ∘ S.Xi2 =ᶠ[𝓝 z] S.Xi1 := by
      filter_upwards [hB.mem_nhds hz] with w hw
      exact hPhiChart w hw
    have hPull : pullbackMetric S.original1 (Phi ∘ S.Xi2) z =
        pullbackMetric S.original1 S.Xi1 z :=
      (pullbackMetric_eventuallyEq_of_eventuallyEq S.original1 _ _ z hNear).eq_of_nhds
    have hCarrier : pullbackMetric (pullbackMetric S.original1 Phi) S.Xi2 z =
        pullbackMetric S.original2 S.Xi2 z := by
      calc
        pullbackMetric (pullbackMetric S.original1 Phi) S.Xi2 z =
            pullbackMetric S.original1 (Phi ∘ S.Xi2) z := hComp.symm
        _ = pullbackMetric S.original1 S.Xi1 z := hPull
        _ = S.g1 z := (S.carrier1 (hRoom hz)).symm
        _ = S.g2 z := hMetric hz
        _ = pullbackMetric S.original2 S.Xi2 z := S.carrier2 (hRoom hz)
    let J := coordinateJacobianMatrix S.Xi2 z
    have hJ : IsUnit J.det := S.Xi2_jacobian z (hRoom hz)
    have hJT : IsUnit Jᵀ.det := by simpa only [Matrix.det_transpose] using hJ
    have hCong : Jᵀ * (pullbackMetric S.original1 Phi x) * J =
        Jᵀ * S.original2 x * J := by
      simpa only [J, hxz, pullbackMetric_eq_coordinate_form] using hCarrier
    have hCancel := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      (Jᵀ)⁻¹ * M * J⁻¹) hCong
    simp only [Matrix.mul_assoc] at hCancel
    rw [Matrix.nonsing_inv_mul_cancel_left (A := Jᵀ) _ hJT,
      Matrix.nonsing_inv_mul_cancel_left (A := Jᵀ) _ hJT] at hCancel
    simpa only [Matrix.mul_nonsing_inv J hJ, Matrix.mul_one] using hCancel
  have hPhiJac : ∀ x ∈ Z, IsUnit (coordinateJacobianMatrix Phi x).det := by
    intro x hx
    have hForm : S.original2 x =
        (coordinateJacobianMatrix Phi x)ᵀ * S.original1 (Phi x) *
          coordinateJacobianMatrix Phi x := by
      rw [← hMetricPhysical hx]
      exact pullbackMetric_eq_coordinate_form S.original1 Phi x
    exact isUnit_det_of_posDef_pullback _ _ _ (S.original2_admissible.posDef x) hForm
  have hSources : ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ), ∀ x ∈ Z,
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original1
        S.original1_admissible s (Phi x) =
      radiusTwoSmoothSourceResponse S.hreg S.hcalc S.original2
        S.original2_admissible s x := by
    intro s x hx
    let z := e.symm x
    have hz : z ∈ B := hInvRoom x hx
    have hxz : S.Xi2 z = x := by simpa only [he] using e.right_inv hx
    rw [← hxz, hPhiChart z hz]
    exact hAll s hz
  refine ⟨Z, Phi, hTarget, hZopen, hZconn, ?_, hZrange, hPhiSmooth, hPhiInj,
    hPhiRange, hPhiJac, hMetricPhysical, hSources, hPhiChart⟩
  change e 0 ∈ e.target
  exact e.map_source (show (0 : R3) ∈ e.source by simpa only [hSource] using mem_ball_self hr)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
