import Calderon.SourceResponseEuclideanChart
import Calderon.CollaboratorFixedDirichletRegularityOct17
import Calderon.CollaboratorFixedSobolevCalculusOct17
import Mathlib.Topology.NhdsWithin

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Distributions
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily ExteriorSource

theorem exists_common_source_chart_known_room
    (g1 g2 : MatrixField) (hg1 : IsAdmissibleMetric g1) (hg2 : IsAdmissibleMetric g2)
    (c : Fin 3 → 𝓓(fixedExteriorSourceOpens, ℝ))
    (e1 e2 : OpenPartialHomeomorph R3 R3)
    (hCoordinates1 : (e1 : R3 → R3) = radiusTwoSourceEuclideanCoordinates
      fixedDirichletRegularity fixedSobolevCalculus g1 hg1 c)
    (hCoordinates2 : (e2 : R3 → R3) = radiusTwoSourceEuclideanCoordinates
      fixedDirichletRegularity fixedSobolevCalculus g2 hg2 c)
    (p q : R3) (hp : p ∈ e2.source) (hq : q ∈ e1.source)
    (hCenter1 : e1 q = 0) (hCenter2 : e2 p = 0)
    (W : Set R3) (hW : IsOpen W) (hpClosure : p ∈ closure W)
    (Phi : R3 → R3) (hLimit : Tendsto Phi (nhdsWithin p W) (nhds q))
    (hMatch : ∀ y ∈ W, ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        g1 hg1 s (Phi y) =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        g2 hg2 s y)
    (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r0 ∧
      ball (0 : R3) r ⊆ e1.target ∩ e2.target ∧
      IsOpen (ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W) ∧
      (0 : R3) ∈ closure (ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W) ∧
      (∀ z ∈ ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W,
        Phi (e2.symm z) = e1.symm z) ∧
      ∀ s : 𝓓(fixedExteriorSourceOpens, ℝ),
        ∀ z ∈ ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W,
          radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
            g1 hg1 s (e1.symm z) =
          radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
            g2 hg2 s (e2.symm z) := by
  have hNear : {y : R3 | Phi y ∈ e1.source} ∈ nhdsWithin p W :=
    hLimit (e1.open_source.mem_nhds hq)
  obtain ⟨T, hT, hpT, hTW⟩ := mem_nhdsWithin.mp hNear
  have h0T1 : (0 : R3) ∈ e1.target := by
    simpa only [hCenter1] using e1.map_source hq
  have h0T2 : (0 : R3) ∈ e2.target := by
    simpa only [hCenter2] using e2.map_source hp
  have hX20 : e2.symm (0 : R3) = p := by
    simpa only [hCenter2] using e2.left_inv hp
  have hR : IsOpen (e1.target ∩ (e2.target ∩ (e2.symm : R3 → R3) ⁻¹' T)) :=
    e1.open_target.inter (e2.isOpen_inter_preimage_symm hT)
  have h0R : (0 : R3) ∈ e1.target ∩ (e2.target ∩ (e2.symm : R3 → R3) ⁻¹' T) := by
    refine ⟨h0T1, h0T2, ?_⟩
    change e2.symm (0 : R3) ∈ T
    rw [hX20]
    exact hpT
  obtain ⟨r1, hr1, hBall⟩ := Metric.mem_nhds_iff.mp (hR.mem_nhds h0R)
  obtain ⟨r, hr, hrr0, hBallR⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ r0 ∧
      ball (0 : R3) r ⊆ e1.target ∩ (e2.target ∩ (e2.symm : R3 → R3) ⁻¹' T) :=
    ⟨min r1 r0, lt_min hr1 hr0, min_le_right r1 r0,
      (Metric.ball_subset_ball (min_le_left r1 r0)).trans hBall⟩
  have hBallTargets : ball (0 : R3) r ⊆ e1.target ∩ e2.target :=
    fun z hz => ⟨(hBallR hz).1, (hBallR hz).2.1⟩
  have hSymmBall : ContinuousOn (e2.symm : R3 → R3) (ball (0 : R3) r) :=
    e2.continuousOn_symm.mono fun z hz => (hBallTargets hz).2
  have hKnownOpen : IsOpen (ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W) :=
    hSymmBall.isOpen_inter_preimage Metric.isOpen_ball hW
  have hPoint (y : R3) (hy : y ∈ W) : e1 (Phi y) = e2 y := by
    have hValues : radiusTwoSourceCoordinates fixedDirichletRegularity fixedSobolevCalculus
        g1 hg1 c (Phi y) = radiusTwoSourceCoordinates fixedDirichletRegularity
        fixedSobolevCalculus g2 hg2 c y := by
      funext i
      exact hMatch y hy (c i)
    simpa only [hCoordinates1, hCoordinates2, radiusTwoSourceEuclideanCoordinates] using
      congrArg (fun v : Fin 3 → ℝ => (EuclideanSpace.equiv (Fin 3) ℝ).symm v) hValues
  have hBranch (z : R3) (hz : z ∈ ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W) :
      Phi (e2.symm z) = e1.symm z := by
    have hzT2 : z ∈ e2.target := (hBallTargets hz.1).2
    have hyT : e2.symm z ∈ T := (hBallR hz.1).2.2
    have hyW : e2.symm z ∈ W := hz.2
    have hSource : Phi (e2.symm z) ∈ e1.source := hTW ⟨hyT, hyW⟩
    calc
      Phi (e2.symm z) = e1.symm (e1 (Phi (e2.symm z))) := (e1.left_inv hSource).symm
      _ = e1.symm (e2 (e2.symm z)) := by rw [hPoint (e2.symm z) hyW]
      _ = e1.symm z := by rw [e2.right_inv hzT2]
  have hSourceEqual (s : 𝓓(fixedExteriorSourceOpens, ℝ)) (z : R3)
      (hz : z ∈ ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W) :
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        g1 hg1 s (e1.symm z) =
      radiusTwoSmoothSourceResponse fixedDirichletRegularity fixedSobolevCalculus
        g2 hg2 s (e2.symm z) := by
    rw [← hBranch z hz]
    exact hMatch (e2.symm z) hz.2 s
  have hV : IsOpen (e2.source ∩ (e2 : R3 → R3) ⁻¹' ball (0 : R3) r) :=
    e2.isOpen_inter_preimage Metric.isOpen_ball
  have hpV : p ∈ e2.source ∩ (e2 : R3 → R3) ⁻¹' ball (0 : R3) r := by
    refine ⟨hp, ?_⟩
    change e2 p ∈ ball (0 : R3) r
    rw [hCenter2]
    exact Metric.mem_ball_self hr
  have hpVW : p ∈ closure ((e2.source ∩ (e2 : R3 → R3) ⁻¹' ball (0 : R3) r) ∩ W) := by
    refine _root_.mem_closure_iff.mpr ?_
    intro o ho hpo
    obtain ⟨x, ⟨hxo, hxV⟩, hxW⟩ :=
      _root_.mem_closure_iff.mp hpClosure (o ∩ (e2.source ∩ (e2 : R3 → R3) ⁻¹' ball (0 : R3) r))
        (ho.inter hV) ⟨hpo, hpV⟩
    exact ⟨x, hxo, hxV, hxW⟩
  have hImage : (e2 : R3 → R3) '' ((e2.source ∩ (e2 : R3 → R3) ⁻¹' ball (0 : R3) r) ∩ W) ⊆
      ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W := by
    rintro z ⟨y, ⟨⟨hyS, hyB⟩, hyW⟩, rfl⟩
    refine ⟨hyB, ?_⟩
    change e2.symm (e2 y) ∈ W
    rw [e2.left_inv hyS]
    exact hyW
  have h0Closure : (0 : R3) ∈ closure (ball (0 : R3) r ∩ (e2.symm : R3 → R3) ⁻¹' W) := by
    have hMapped := closure_mono hImage (mem_closure_image (e2.continuousAt hp) hpVW)
    rw [hCenter2] at hMapped
    exact hMapped
  exact ⟨r, hr, hrr0, hBallTargets, hKnownOpen, h0Closure, hBranch, hSourceEqual⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
