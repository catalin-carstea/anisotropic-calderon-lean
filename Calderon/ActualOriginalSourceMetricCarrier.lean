import Calderon.ActualOriginalSourceMetricPhysical
import Calderon.MetricPullbackComposition

set_option autoImplicit false
noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge ExteriorSource ConnectionError MetricVolume MetricOperator ConformalDepth

theorem pullbackMetric_original_source_extension_eq_model
    (S : KnownSideSourceData) (L : ℝ) (cover : NativeNormalCover S L)
    (i : Fin cover.count) (lam : ℝ) (hlam : 0 < lam) (hlamRoom : lam ≤ cover.dilationCeiling)
    (y : R3) (hy : y ∈ (cover.packet i).centers)
    (r : ℝ) (hrpos : 0 < r) (hrceil : r < cover.radiusCeiling)
    (Fext : R3 → R3)
    (hNear : ∀ z ∈ closedBall (0 : R3) 2, Fext =ᶠ[𝓝 z]
      (fun w => S.Xi1 (lam • packetEndpoint S L (cover.packet i) lam y r w)))
    (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    pullbackMetric S.original1 Fext z = originalSourcePacketMetricModel S L (cover.packet i) lam y r z := by
  let P := cover.packet i
  let X : R3 → R3 := packetEndpoint S L P lam y r
  let D : R3 → R3 := fun x => lam • x
  let Q : R3 → R3 := fun x => lam • X x
  have hq : lam ∈ Icc (0 : ℝ) cover.dilationCeiling := ⟨hlam.le,hlamRoom⟩
  have hRoom : Q z ∈ S.coordinateRoom := cover.coordinate_room i lam hq y hy r hrpos hrceil z hz
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ X :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hQ : ContDiff ℝ ∞ Q := ContDiff.const_smul lam hX
  have hXi : DifferentiableAt ℝ S.Xi1 (Q z) :=
    (S.Xi1_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds hRoom)).differentiableAt (by simp)
  have hD : ContDiff ℝ ∞ D := ContDiff.const_smul lam contDiff_id
  have hCarrier : pullbackMetric (pullbackMetric S.original1 S.Xi1) Q z = pullbackMetric S.g1 Q z := by
    rw [pullbackMetric_eq_coordinate_form (pullbackMetric S.original1 S.Xi1) Q z,
      pullbackMetric_eq_coordinate_form S.g1 Q z]
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ =>
      (coordinateJacobianMatrix Q z).transpose * M * coordinateJacobianMatrix Q z)
      (S.carrier1 hRoom).symm
  have hDil : pullbackMetric S.g1 D = fun x => lam^2 • S.g1 (lam • x) :=
    funext (pullbackMetric_dilation S.g1 lam)
  calc
    pullbackMetric S.original1 Fext z = pullbackMetric S.original1 (S.Xi1 ∘ Q) z :=
      (pullbackMetric_eventuallyEq_of_eventuallyEq S.original1 Fext (S.Xi1 ∘ Q) z (hNear z hz)).eq_of_nhds
    _ = pullbackMetric (pullbackMetric S.original1 S.Xi1) Q z :=
      pullbackMetric_comp_of_differentiableAt S.original1 S.Xi1 Q z hXi (hQ.differentiable (by simp) z)
    _ = pullbackMetric S.g1 Q z := hCarrier
    _ = pullbackMetric (pullbackMetric S.g1 D) X z :=
      pullbackMetric_comp_of_differentiableAt S.g1 D X z
        (hD.differentiable (by simp) (X z)) (hX.differentiable (by simp) z)
    _ = lam^2 • pullbackMetric (fun x => S.g1 (lam • x)) X z := by
      rw [hDil,pullbackMetric_const_smul]
    _ = originalSourcePacketMetricModel S L P lam y r z :=
      (originalSourcePacketMetricModel_eq_scaled_physical_pullback S L cover i lam hlam hlamRoom
        y hy r hrpos hrceil z hz).symm

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
