import Calderon.MixedKernelConstruction.MixedKernelAsymmetricInterpolation
import Calderon.MixedKernelConstruction.MixedKernelAsymmetricHeightParameters
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

/-- A constructed native first basis arm, observed strictly on the prescribed positive side,
with exponent as close to one as requested and an actual small physical domain. -/
theorem native_scalar_interpolation_positive_side_near_one
    (g : MatrixField) (hg : IsAdmissibleMetric g) (lam : ℝ) (p : R3) {psi : R3 → ℝ}
    (hpsi : ContDiffAt ℝ 2 psi p) (hpsi0 : psi p = 0)
    (hdpsi : (fun k => pd k psi p) ≠ 0) (r0 : ℝ) (hr0 : 0 < r0)
    (beta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    ∃ (D O T K1 KT : Set R3) (Kint gamma : ℝ),
      IsOpen D ∧ IsConnected D ∧ IsOpen O ∧ p ∈ O ∧ O ⊆ D ∧
      IsOpen T ∧ T.Nonempty ∧ IsCompact K1 ∧ IsCompact KT ∧
      D ⊆ K1 ∧ T ⊆ KT ∧ KT ⊆ D ∧ K1 ⊆ Metric.ball p r0 ∧
      T ⊆ {x | 0 < psi x} ∧ KT ⊆ {x | 0 < psi x} ∧ 1-beta < gamma ∧ gamma < 1 ∧ 0 < Kint ∧
      ∀ (u : Lp ℝ 2 ((volume : Measure R3).restrict D)) (q : R3 → ℝ),
        q =ᵐ[(volume : Measure R3).restrict D] (u : R3 → ℝ) → ContDiffOn ℝ ∞ q D →
        (∀ x ∈ D, Lop (fun i j y => principalCoefficient g (lam • y) i j) q x = 0) →
        ∀ (uO : Lp ℝ 2 ((volume : Measure R3).restrict O))
          (uT : Lp ℝ 2 ((volume : Measure R3).restrict T)),
        q =ᵐ[(volume : Measure R3).restrict O] (uO : R3 → ℝ) →
        q =ᵐ[(volume : Measure R3).restrict T] (uT : R3 → ℝ) →
        ‖uO‖ ≤ Kint*(‖uT‖^gamma*‖u‖^(1-gamma)) := by
  obtain ⟨theta,htheta,hzero,hd,hstrict,c,r,hc,hr,hgap⟩ :=
    exists_srcStrict_phase_known_side (fun x => g (lam • x)) p
      (hg.posDef (lam • p)) hpsi hpsi0 hdpsi
  have hdtheta : (fun k => pd k theta p) ≠ 0 := by
    have heq : (fun k => pd k theta p) = fun k => pd k psi p := funext hd
    rw [heq]
    exact hdpsi
  obtain ⟨e,he,hcenter,k0,hk0,H⟩ := native_room_interpolation_lp_between_dilate
    g hg lam htheta p hzero hdtheta hstrict
      (min r0 r) (lt_min hr0 hr)
  let k := k0/2
  have hk : 0 < k := half_pos hk0
  have hkk0 : k ≤ k0 := half_le_self hk0.le
  obtain ⟨rho,hrho,H2⟩ := H k hk hkk0
  let R := rho/2
  have hR : 0 < R := half_pos hrho
  let l := min (rho/4) (min (c*R^2/18) (1/(16*k)))
  have hl : 0 < l := by dsimp [l]; positivity
  have hlrho : l ≤ rho/4 := min_le_left _ _
  have hlR : l ≤ c*R^2/18 := (min_le_right _ _).trans (min_le_left _ _)
  have hlk : l ≤ 1/(16*k) := (min_le_right _ _).trans (min_le_right _ _)
  have hkl : k*l < 1/8 := by
    have hb := (le_div_iff₀ (by positivity : (0:ℝ) < 16*k)).mp hlk
    nlinarith
  obtain ⟨h,eps,heps,h4,hhl,hepsk,hmargin,hgamma,hgamma1⟩ :=
    exists_asymmetric_height_exponent_close_one hk hl hkl hbeta hbeta1
  have hroom : l+4*eps ≤ rho := by linarith
  have hRrho : R ≤ rho := half_le_self hrho.le
  obtain ⟨hloc,hDt,Kint,hKint,HI⟩ := H2 l h eps R heps h4 hhl hR hroom hRrho hmargin
  obtain ⟨hD,hO,hT,hTne,hOD,hTD,hB,hBD,hH,hHT,hOc,hOcD,hKT,hTKT,hKTD⟩ :=
    native_rooms_between e heps h4 hhl hR hDt
  have hll : 4*eps < l := h4.trans_le hhl
  obtain ⟨hconn,_,_,_,_⟩ := chart_room_facts e heps hll hR hDt
  have hpO := chart_room_contains_center e hcenter.2 heps h4 hR
  have hK1 : IsCompact (e.symm '' PhaseCoordinates.closedD l eps R) :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image_of_continuousOn
      (e.continuousOn_symm.mono hDt)
  have hknown : e.symm '' (PhaseCoordinates.closedStop h eps R ∪ PhaseCoordinates.closedSlat l eps R) ⊆
      {x | 0 < psi x} := by
    rintro x ⟨u,hu,rfl⟩
    have huD : u ∈ PhaseCoordinates.closedD l eps R := by
      rcases hu with hu | hu
      · rcases hu with ⟨hs,hz⟩
        exact ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,
          (closedBall_subset_closedBall (by linarith : 7*R/8 ≤ R)) hz⟩
      · exact PhaseCoordinates.roomD_subset_closedD
          (PhaseCoordinates.closedSlat_subset_roomD heps hll hR hu)
    have hxb : e.symm u ∈ Metric.ball p r :=
      Metric.ball_subset_ball (min_le_right _ _) (hloc ⟨u,huD,rfl⟩)
    have hu1 := e.right_inv (hDt huD)
    rw [he] at hu1
    have hthetaU : theta (e.symm u) = u.1 := congrArg Prod.fst hu1
    have hPU : (fderiv ℝ theta p).ker.orthogonalProjectionOnto (e.symm u-p) = u.2 :=
      congrArg Prod.snd hu1
    have hnorm : ‖u.2‖ ≤ ‖e.symm u-p‖ := by
      rw [← hPU]
      exact Submodule.norm_orthogonalProjectionOnto_apply_le _ _
    have hn : 0 ≤ c*‖e.symm u-p‖^2 := mul_nonneg hc.le (sq_nonneg _)
    apply hgap _ hxb
    rw [hthetaU]
    rcases hu with hu | hu
    · linarith [hu.1.1]
    · have hlow := hu.1.1
      have hnormR : R/3 ≤ ‖e.symm u-p‖ := hu.2.1.trans hnorm
      have hsq : R^2/9 ≤ ‖e.symm u-p‖^2 := by nlinarith
      have hmul := mul_le_mul_of_nonneg_left hsq hc.le
      have hpos : 0 < c*R^2 := mul_pos hc (sq_pos_of_pos hR)
      nlinarith
  refine ⟨_,_,_,_,_,Kint,_,hD,hconn,hO,hpO,hOD,hT,hTne,hK1,hKT,
    image_mono PhaseCoordinates.roomD_subset_closedD,hTKT,hKTD,
    hloc.trans (ball_subset_ball (min_le_left _ _)),hTKT.trans hknown,hknown,hgamma,hgamma1,hKint,?_⟩
  exact HI

theorem native_first_basis_arm_positive_side_near_one
    (S : KnownSideSourceData) (lam : ℝ) (p : R3) {psi : R3 → ℝ}
    (hpsi : ContDiffAt ℝ 2 psi p) (hpsi0 : psi p = 0)
    (hdpsi : (fun k => pd k psi p) ≠ 0) (r0 : ℝ) (hr0 : 0 < r0)
    (beta : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    ∃ (D O T K1 KT : Set R3) (Kint gamma : ℝ),
      IsOpen D ∧ IsConnected D ∧ IsOpen O ∧ p ∈ O ∧ O ⊆ D ∧
      IsOpen T ∧ T.Nonempty ∧ IsCompact K1 ∧ IsCompact KT ∧
      D ⊆ K1 ∧ T ⊆ KT ∧ KT ⊆ D ∧ K1 ⊆ Metric.ball p r0 ∧
      T ⊆ {x | 0 < psi x} ∧ 1-beta < gamma ∧ gamma < 1 ∧ 0 < Kint ∧
      FirstBasisArmOn S lam D O T Kint gamma := by
  obtain ⟨D,O,T,K1,KT,Kint,gamma,hD,hDc,hO,hpO,hOD,hT,hTne,hK1,hKT,
      hDK1,hTKT,hKTD,hK1b,hknown,hknownKT,hgamma,hgamma1,hKint,HI⟩ :=
    native_scalar_interpolation_positive_side_near_one S.g1 S.g1_admissible lam p
      hpsi hpsi0 hdpsi r0 hr0 beta hbeta hbeta1
  refine ⟨D,O,T,K1,KT,Kint,gamma,hD,hDc,hO,hpO,hOD,hT,hTne,hK1,hKT,
    hDK1,hTKT,hKTD,hK1b,hknown,hgamma,hgamma1,hKint,?_⟩
  apply first_basis_arm_on_of_room S lam _ _ _
  intro u q hq hqs hP uO uS hqO hqS
  exact HI u q hq hqs (fun x hx =>
    (coordinateFluxDivergence_metricDivergenceFlux_eq_Lop _ q x).symm.trans (hP x hx))
    uO uS hqO hqS

/-- At the actual scaled separating surface the first observation lies in the literal W.
All rooms, buffers and the exponent are constructed, with any requested physical locality. -/
theorem native_first_known_side_arm_near_one (S : KnownSideSourceData) :
    ∃ a : ℝ, 0 < a ∧ ∀ lam : ℝ, 0 < lam → ∀ p : R3,
      lam • p ∈ Metric.ball (0 : R3) a → S.separating_function (lam • p) = 0 →
      ∀ r0 : ℝ, 0 < r0 → ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      ∃ (D O T K1 KT : Set R3) (Kint gamma : ℝ),
        IsOpen D ∧ IsConnected D ∧ IsOpen O ∧ p ∈ O ∧ O ⊆ D ∧
        IsOpen T ∧ T.Nonempty ∧ IsCompact K1 ∧ IsCompact KT ∧
        D ⊆ K1 ∧ T ⊆ KT ∧ KT ⊆ D ∧ K1 ⊆ Metric.ball p r0 ∧
        (∀ x ∈ K1, lam • x ∈ S.coordinateRoom) ∧
        (∀ x ∈ T, lam • x ∈ S.W) ∧ 1-beta < gamma ∧ gamma < 1 ∧ 0 < Kint ∧
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
      hDK1,hTKT,hKTD,hK1b,hknown,hgamma,hgamma1,hKint,hArm⟩ :=
    native_first_basis_arm_positive_side_near_one S lam p hpsi hpsi0 hdpsi r hr beta hbeta hbeta1
  refine ⟨D,O,T,K1,KT,Kint,gamma,hD,hDc,hO,hpO,hOD,hT,hTne,hK1,hKT,
    hDK1,hTKT,hKTD,(fun x hx => (hsmall (hK1b hx)).2),
    (fun x hx => hball (hsmall (hK1b hx)).1),?_,hgamma,hgamma1,hKint,hArm⟩
  intro x hx
  apply hW
  refine ⟨(hsmall (hK1b (hDK1 (hKTD (hTKT hx))))).1,?_⟩
  have hp := hknown hx
  change 0 < -S.separating_function (lam • x) at hp
  linarith

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
