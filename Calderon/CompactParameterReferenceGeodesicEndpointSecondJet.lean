import Calderon.CompactParameterGeodesicEndpointSecondJet
import Calderon.ConformalReferenceOperators

/-! Exact reference specialization of the same joint flow with
endpoint first jet and the pure-velocity Hessian equal to the negative connection. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open MetricOperator
private instance instCompleteCompactReferenceJetR3 : CompleteSpace R3 :=
  FiniteDimensional.complete ℝ R3

theorem conformalReference_coordinateConnection_symmetric
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ) (y v w : R3) :
    coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q)) y v w =
    coordinateConnectionField
      (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
      (metricOperatorField (conformalReferenceMatrix g L q)) y w v := by
  let M : R3 → R3 →L[ℝ] R3 := metricOperatorField (conformalReferenceMatrix g L q)
  have hM : ContDiff ℝ ∞ M := (conformalReference_slice_data g hg L q).1
  have hs : ∀ x u z, inner ℝ (M x u) z = inner ℝ (M x z) u :=
    fun x u z => conformalReferenceOperatorJoint_symmetric g hg L (q,x) u z
  have hD (u a b : R3) :
      inner ℝ (fderiv ℝ M y u a) b = inner ℝ (fderiv ℝ M y u b) a :=
    inverse_metric_derivative_symmetric M (fderiv ℝ M y) y
      (hM.differentiable (by simp) y).hasFDerivAt (.of_forall hs) u a b
  simp only [coordinateConnectionField_apply]
  exact coordinateConnection_symmetric _ _ hD v w

theorem exists_smooth_conformalReference_geodesic_endpoint_velocity_secondJet
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3) :
    ∃ (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)),
      IsOpen B ∧ (y0,0) ∈ B ∧
      ContDiff ℝ ∞ (fun p : (ℝ × (R3 × R3)) × ℝ => Φ p.1.1 p.1.2 p.2) ∧
      (∀ q z, Φ q z 0 = z) ∧
      (∀ q z t u, Φ q z (t + u) = Φ q (Φ q z t) u) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, (y,0) ∈ B → ∀ t, Φ q (y,0) t = (y,0)) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivAt (Φ q z)
          (geodesicPhaseField
            (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
            (metricOperatorField (conformalReferenceMatrix g L q)) (Φ q z t)) t) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, (y,0) ∈ B → (Φ q (y,0) 1).1 = y) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y, (y,0) ∈ B →
        HasFDerivAt (fun z => (Φ q z 1).1)
          (ContinuousLinearMap.fst ℝ R3 R3 + ContinuousLinearMap.snd ℝ R3 R3) (y,0)) ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ y, (y,0) ∈ B → ∀ v w : R3,
        fderiv ℝ (fderiv ℝ (fun z => (Φ q z 1).1)) (y,0) (0,w) (0,v) =
          -coordinateConnectionField
            (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
            (metricOperatorField (conformalReferenceMatrix g L q)) y v w := by
  let M : ℝ × R3 → R3 →L[ℝ] R3 := conformalReferenceOperatorJoint g L
  let Q : ℝ × R3 → R3 →L[ℝ] R3 := fun p => Ring.inverse (M p)
  obtain ⟨Φ,B,hB,hy0,hΦ,hinit,hadd,hstat,hODE,hend,hvalue,hfirst,hsecond⟩ :=
    exists_smooth_parameter_geodesic_endpoint_secondJet Q M
      (contDiff_conformalReferenceInverseJoint g hg L)
      (contDiff_conformalReferenceOperatorJoint g hg L) (Icc (0 : ℝ) 1) isCompact_Icc y0
  refine ⟨Φ,B,hB,hy0,hΦ,hinit,hadd,hstat,?_,hend,hvalue,hfirst,?_⟩
  · intro q hq z hz t ht
    have hQq : (fun y : R3 => Q (q,y)) =
        inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)) := rfl
    have hMq : (fun y : R3 => M (q,y)) =
        metricOperatorField (conformalReferenceMatrix g L q) := rfl
    have hODEq := hODE q hq z hz t ht
    rw [hQq, hMq] at hODEq
    exact hODEq
  · intro q hq y hy v w
    let Γ : R3 →L[ℝ] R3 →L[ℝ] R3 :=
      coordinateConnectionField
        (inverseMetricField (metricOperatorField (conformalReferenceMatrix g L q)))
        (metricOperatorField (conformalReferenceMatrix g L q)) y
    have hh := hsecond q hq y hy (0,v) (0,w)
    change fderiv ℝ (fderiv ℝ (fun z => (Φ q z 1).1)) (y,0) (0,w) (0,v) =
      -(1/2 : ℝ) • (Γ v w + Γ w v) at hh
    have hs : Γ w v = Γ v w := conformalReference_coordinateConnection_symmetric g hg L q y w v
    rw [hs] at hh
    have halg : -(1/2 : ℝ) • (Γ v w + Γ v w) = -Γ v w := by
      rw [smul_add,← add_smul]
      norm_num
    exact hh.trans halg
end OAI.AnisotropicCalderon.ConnectionError
