import Calderon.MixedKernelConstruction.MixedKernelKnownSideNearOne
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation

/-- Retain strict positivity on the ENTIRE actual compact data buffer. -/
theorem native_first_basis_arm_compact_positive_side_near_one
    (S : KnownSideSourceData) (lam : ℝ) (p : R3) {psi : R3 → ℝ}
    (hpsi : ContDiffAt ℝ 2 psi p) (hpsi0 : psi p = 0)
    (hdpsi : (fun k => pd k psi p) ≠ 0) (r0 : ℝ) (hr0 : 0 < r0)
    (beta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    ∃ (D O T K1 KT : Set R3) (Kint gamma : ℝ),
      IsOpen D ∧ IsConnected D ∧ IsOpen O ∧ p ∈ O ∧ O ⊆ D ∧
      IsOpen T ∧ T.Nonempty ∧ IsCompact K1 ∧ IsCompact KT ∧
      D ⊆ K1 ∧ T ⊆ KT ∧ KT ⊆ D ∧ K1 ⊆ Metric.ball p r0 ∧
      T ⊆ {x | 0 < psi x} ∧ KT ⊆ {x | 0 < psi x} ∧ 1-beta < gamma ∧ gamma < 1 ∧ 0 < Kint ∧
      FirstBasisArmOn S lam D O T Kint gamma := by
  obtain ⟨D,O,T,K1,KT,Kint,gamma,hD,hDc,hO,hpO,hOD,hT,hTne,hK1,hKT,
      hDK1,hTKT,hKTD,hK1b,hknown,hknownKT,hgamma,hgamma1,hKint,HI⟩ :=
    native_scalar_interpolation_positive_side_near_one S.g1 S.g1_admissible lam p
      hpsi hpsi0 hdpsi r0 hr0 beta hbeta hbeta1
  refine ⟨D,O,T,K1,KT,Kint,gamma,hD,hDc,hO,hpO,hOD,hT,hTne,hK1,hKT,
    hDK1,hTKT,hKTD,hK1b,hknown,hknownKT,hgamma,hgamma1,hKint,?_⟩
  apply first_basis_arm_on_of_room S lam _ _ _
  intro u q hq hqs hP uO uS hqO hqS
  exact HI u q hq hqs (fun x hx =>
    (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ q x).symm.trans (hP x hx))
    uO uS hqO hqS


/-- Both open observation and its complete compact buffer lie in the original scaled W. -/
theorem native_first_known_side_compact_arm_near_one (S : KnownSideSourceData) :
    ∃ a : ℝ, 0 < a ∧ ∀ lam : ℝ, 0 < lam → ∀ p : R3,
      lam • p ∈ Metric.ball (0 : R3) a → S.separating_function (lam • p) = 0 →
      ∀ r0 : ℝ, 0 < r0 → ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      ∃ (D O T K1 KT : Set R3) (Kint gamma : ℝ),
        IsOpen D ∧ IsConnected D ∧ IsOpen O ∧ p ∈ O ∧ O ⊆ D ∧
        IsOpen T ∧ T.Nonempty ∧ IsCompact K1 ∧ IsCompact KT ∧
        D ⊆ K1 ∧ T ⊆ KT ∧ KT ⊆ D ∧ K1 ⊆ Metric.ball p r0 ∧
        (∀ x ∈ K1, lam • x ∈ S.coordinateRoom) ∧
        (∀ x ∈ T, lam • x ∈ S.W) ∧ (∀ x ∈ KT, lam • x ∈ S.W) ∧ 1-beta < gamma ∧ gamma < 1 ∧ 0 < Kint ∧
        FirstBasisArmOn S lam D O T Kint gamma := by
  obtain ⟨a,ha,hball,hW,hnc⟩ := separating_noncritical_ball S
  refine ⟨a,ha,fun lam hlam p hp hp0 r0 hr0 beta hbeta hbeta1 => ?_⟩
  have hdp := hnc _ hp
  have hcd : ContDiffAt ℝ ∞ S.separating_function (lam • p) :=
    S.separating_function_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds (hball hp))
  have hpsi : ContDiffAt ℝ 2 (fun x : R3 => -S.separating_function (lam • x)) p :=
    ((hcd.comp p (contDiffAt_id.const_smul lam)).neg).of_le (by simp)
  have hpsi0 : (fun x : R3 => -S.separating_function (lam • x)) p = 0 := by simp [hp0]
  have hF : HasFDerivAt (fun x : R3 => -S.separating_function (lam • x))
      (-((fderiv ℝ S.separating_function (lam • p)).comp
        (lam • ContinuousLinearMap.id ℝ R3))) p :=
    ((hcd.differentiableAt (by simp)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).const_smul lam)).neg
  have hdk : ∀ k, pd k (fun x : R3 => -S.separating_function (lam • x)) p =
      -(lam * fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1)) := by
    intro k
    unfold pd
    rw [hF.fderiv]
    simp
  have hdpsi : (fun k => pd k (fun x : R3 => -S.separating_function (lam • x)) p) ≠ 0 := by
    intro h
    apply hdp
    ext v
    rw [clm_apply_eq_sum_pd]
    simp only [ContinuousLinearMap.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk := congrFun h k
    simp only [Pi.zero_apply] at hk
    rw [hdk k] at hk
    have hz : fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1) = 0 := by
      have hz' : lam * fderiv ℝ S.separating_function (lam • p) (EuclideanSpace.single k 1) = 0 := by
        linarith
      exact (mul_eq_zero.mp hz').resolve_left hlam.ne'
    rw [hz,zero_mul]
  let U0 : Set R3 := {x | lam • x ∈ Metric.ball (0 : R3) a} ∩ Metric.ball p r0
  have hU0 : IsOpen U0 :=
    (isOpen_ball.preimage (continuous_id.const_smul lam)).inter isOpen_ball
  have hpU0 : p ∈ U0 := ⟨hp,mem_ball_self hr0⟩
  obtain ⟨r,hr,hsmall⟩ := Metric.isOpen_iff.mp hU0 p hpU0
  obtain ⟨D,O,T,K1,KT,Kint,gamma,hD,hDc,hO,hpO,hOD,hT,hTne,hK1,hKT,
      hDK1,hTKT,hKTD,hK1b,hknown,hknownKT,hgamma,hgamma1,hKint,hArm⟩ :=
    native_first_basis_arm_compact_positive_side_near_one S lam p hpsi hpsi0 hdpsi r hr beta hbeta hbeta1
  have hKTW : ∀ x ∈ KT, lam • x ∈ S.W := by
    intro x hx
    apply hW
    refine ⟨(hsmall (hK1b (hDK1 (hKTD hx)))).1,?_⟩
    have hh := hknownKT hx
    change 0 < -S.separating_function (lam • x) at hh
    linarith
  exact ⟨D,O,T,K1,KT,Kint,gamma,hD,hDc,hO,hpO,hOD,hT,hTne,hK1,hKT,
    hDK1,hTKT,hKTD,(fun x hx => (hsmall (hK1b hx)).2),
    (fun x hx => hball (hsmall (hK1b hx)).1),
    (fun x hx => hKTW x (hTKT hx)),hKTW,hgamma,hgamma1,hKint,hArm⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
