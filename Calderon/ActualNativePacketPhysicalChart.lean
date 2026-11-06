import Calderon.ActualReferencePhysicalOrientation
import Calderon.JointParameterFiberChart
import Calderon.ActualMixedKernelSurfaceHomotopyRoom

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume

theorem isInvertible_of_operatorMatrixMap_det_ne_zero (A : R3 →L[ℝ] R3)
    (hA : (operatorMatrixMap A).det ≠ 0) : A.IsInvertible := by
  have hm : IsUnit (operatorMatrixMap A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hA)
  have ha : IsUnit A := by
    have hu := hm.map matrixOperatorAlgEquiv.toMonoidHom
    have hRound : matrixOperatorAlgEquiv (operatorMatrixMap A) = A := by
      change matrixOperatorAlgEquiv (matrixOperatorAlgEquiv.symm A) = A
      exact matrixOperatorAlgEquiv.apply_symm_apply A
    change IsUnit (matrixOperatorAlgEquiv (operatorMatrixMap A)) at hu
    rw [hRound] at hu
    exact hu
  obtain ⟨u,hu⟩ := ha
  refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ R3 u,?_⟩
  change (u : R3 →L[ℝ] R3) = A
  exact hu

theorem exists_fixed_physical_chart_of_injOn_isInvertible
    (X : R3 → R3) (hX : ContDiff ℝ ∞ X) (hInj : InjOn X (ball (0 : R3) 2))
    (hInv : ∀ z ∈ ball (0 : R3) 2, (fderiv ℝ X z).IsInvertible) :
    ∃ e : OpenPartialHomeomorph R3 R3, (e : R3 → R3) = X ∧
      e.source = ball (0 : R3) 2 ∧ e.target = X '' ball (0 : R3) 2 ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ b ∈ X '' closedBall (0 : R3) 1, ‖iteratedFDeriv ℝ j e.symm b‖ ≤ D := by
  let W := ball (0 : R3) 2
  have hW : IsOpen W := isOpen_ball
  have hOpen : IsOpenMap (W.domRestrict X) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    obtain ⟨D,hD⟩ := hInv x x.property
    have hd : HasFDerivAt X (D : R3 →L[ℝ] R3) (x : R3) := by
      rw [hD]
      exact (hX.differentiable (by simp) (x : R3)).hasFDerivAt
    have hm : Filter.map X (𝓝 (x : R3)) = 𝓝 (X (x : R3)) :=
      (hX.contDiffAt.hasStrictFDerivAt' hd (by simp)).map_nhds_eq_of_equiv
    have hs : Filter.map ((↑) : W → R3) (𝓝 x) = 𝓝 (x : R3) :=
      map_nhds_subtype_coe_eq_nhds x.property (hW.mem_nhds x.property)
    change 𝓝 (X (x : R3)) ≤ Filter.map (X ∘ ((↑) : W → R3)) (𝓝 x)
    rw [← Filter.map_map,hs,hm]
  let pe : PartialEquiv R3 R3 := hInj.toPartialEquiv X W
  let e : OpenPartialHomeomorph R3 R3 :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict pe hX.continuous.continuousOn hOpen hW
  have he : (e : R3 → R3) = X := rfl
  have hs : e.source = W := rfl
  have ht : e.target = X '' W := rfl
  have hSmooth : ContDiffOn ℝ ∞ e.symm e.target := by
    intro b hb
    have ha : e.symm b ∈ W := by simpa only [hs] using e.map_target hb
    obtain ⟨D,hD⟩ := hInv (e.symm b) ha
    have hd : HasFDerivAt e (D : R3 →L[ℝ] R3) (e.symm b) := by
      change HasFDerivAt X (D : R3 →L[ℝ] R3) (e.symm b)
      rw [hD]
      exact (hX.differentiable (by simp) (e.symm b)).hasFDerivAt
    exact (e.contDiffAt_symm hb hd hX.contDiffAt).contDiffWithinAt
  refine ⟨e,he,hs,ht,hSmooth,?_⟩
  apply exists_compact_uniform_iteratedFDeriv_bound_on_open e.symm e.target e.open_target hSmooth
    (X '' closedBall (0 : R3) 1) ((isCompact_closedBall _ _).image hX.continuous)
  rw [ht]
  apply image_mono
  intro z hz
  have hz' : dist z (0 : R3) ≤ 1 := hz
  change dist z (0 : R3) < 2
  linarith

end OAI.AnisotropicCalderon.ConnectionError

namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConnectionError EnergyBridge MetricOperator MetricVolume

theorem exists_actual_native_packet_physical_chart
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling) :
    ∃ e : OpenPartialHomeomorph R3 R3,
      (e : R3 → R3) = packetEndpoint S L (cover.packet i) q y r ∧
      e.source = ball (0 : R3) 2 ∧
      e.target = packetEndpoint S L (cover.packet i) q y r '' ball (0 : R3) 2 ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ N : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
        ∀ b ∈ packetEndpoint S L (cover.packet i) q y r '' closedBall (0 : R3) 1,
          ‖iteratedFDeriv ℝ j e.symm b‖ ≤ D := by
  let P := cover.packet i
  let X : R3 → R3 := packetEndpoint S L P q y r
  have hq1 : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1,hq.2.trans cover.dilation_le_one⟩
  have hc : ‖y-P.y0‖ ≤ 4*P.rho := (P.centers_room y hy).1.le
  have hr : |r| ≤ 4*P.rho := by
    rw [abs_of_pos hrpos]
    exact (hrceil.trans (cover.radius_room i)).le
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hInj : InjOn X (ball (0 : R3) 2) :=
    (cover.normal_injective i q hq y hy r hrpos hrceil).mono ball_subset_closedBall
  have hInv : ∀ z ∈ ball (0 : R3) 2, (fderiv ℝ X z).IsInvertible := by
    intro z hz
    apply isInvertible_of_operatorMatrixMap_det_ne_zero
    have hd := coordinateJacobianMatrix_referencePhysicalEndpoint_det_pos
      S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
      q hq1 y hc r hr hrpos z (ball_subset_closedBall hz)
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap] at hd
    exact hd.ne'
  exact exists_fixed_physical_chart_of_injOn_isInvertible X hX hInj hInv

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
