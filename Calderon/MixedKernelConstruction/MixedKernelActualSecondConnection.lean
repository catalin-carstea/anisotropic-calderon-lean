import Calderon.MixedKernelConstruction.MixedKernelActualNormalizedOperatorDictionary
import Calderon.MixedKernelConstruction.MixedKernelInverseFirstJet
import Calderon.MixedKernelConstruction.MixedKernelConnectionPerturbation
import Calderon.MixedKernelConstruction.MixedKernelNativeReferenceAngularBounds
import Calderon.MixedKernelConstruction.MixedKernelCylinderBoundary
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError MetricOperator ConformalDepth
open NormalizedPrincipalMetric
open scoped ContDiff Topology

/-- A genuine unit operator is exactly its own double inverse. -/
theorem ring_inverse_inverse_of_isUnit (A : R3 →L[ℝ] R3) (hA : IsUnit A) :
    Ring.inverse (Ring.inverse A)=A := by
  obtain ⟨u,hu⟩ := hA
  rw [← hu,Ring.inverse_unit,Ring.inverse_unit]
  rfl

/-- Compact reference value and first-jet bounds are chosen before all current-radius parameters. -/
theorem exists_reference_principal_operator_first_jet_bound (S : KnownSideSourceData) (L : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ lam ∈ Icc (0 : ℝ) 1, ∀ y ∈ cylinder,
      let G := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
      let A0 := fun Y => Ring.inverse (G Y)
      ‖G y‖ ≤ K ∧ ‖A0 y‖ ≤ K ∧ ‖fderiv ℝ A0 y‖ ≤ K := by
  let room : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall (0 : R3) 2
  have hRoom : IsCompact room := isCompact_Icc.prod (isCompact_closedBall _ _)
  let GJ := conformalReferenceOperatorJoint S.g1 L
  let AJ := fun a : ℝ × R3 => Ring.inverse (GJ a)
  have hGJ := contDiff_conformalReferenceOperatorJoint S.g1 S.g1_admissible L
  have hAJ := contDiff_conformalReferenceInverseJoint S.g1 S.g1_admissible L
  obtain ⟨g,hg⟩ := hRoom.exists_bound_of_continuousOn hGJ.continuous.continuousOn
  obtain ⟨a,ha⟩ := hRoom.exists_bound_of_continuousOn hAJ.continuous.continuousOn
  obtain ⟨da,hda⟩ := hRoom.exists_bound_of_continuousOn
    (contDiff_jointSpatialDerivative AJ hAJ).continuous.continuousOn
  let K : ℝ := |g|+|a|+|da|+1
  have hK : 1 ≤ K := by dsimp [K];linarith [abs_nonneg g,abs_nonneg a,abs_nonneg da]
  have hgK : g ≤ K := by dsimp [K];linarith [le_abs_self g,abs_nonneg a,abs_nonneg da]
  have haK : a ≤ K := by dsimp [K];linarith [le_abs_self a,abs_nonneg g,abs_nonneg da]
  have hdaK : da ≤ K := by dsimp [K];linarith [le_abs_self da,abs_nonneg g,abs_nonneg a]
  refine ⟨K,hK,?_⟩
  intro lam hlam y hy G A0
  have hp : (lam,y) ∈ room := ⟨hlam,by
    simpa only [mem_closedBall,dist_zero_right] using norm_le_two_of_mem_cylinder y hy⟩
  refine ⟨(hg (lam,y) hp).trans hgK,(ha (lam,y) hp).trans haK,?_⟩
  have hb := (hda (lam,y) hp).trans hdaK
  dsimp only [AJ] at hb
  rw [jointSpatialDerivative_eq_fderiv_slice _ hAJ lam y] at hb
  exact hb

/-- The SAME actual normalized second connection is quantitatively close to the reference connection. -/
theorem exists_actual_normalized_second_connection_error_bound
    (S : KnownSideSourceData) (L : ℝ) :
    ∃ C t : ℝ, 0 < C ∧ 0 < t ∧ ∀ lam ∈ Icc (0 : ℝ) 1,
      ∀ (delta Rstar eps : ℝ) (p : ℕ), CurrentRadiusBootstrap S L lam delta Rstar eps p →
      ∀ y ∈ cylinder, eps*referenceRadius delta Rstar p L y ≤ t →
      let G := metricOperatorField (conformalReferenceMatrix S.g1 L lam)
      let M := metricOperatorField (fun Y => (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam Y)⁻¹)
      ‖coordinateConnectionField (inverseMetricField M) M y-
        coordinateConnectionField (inverseMetricField G) G y‖ ≤
          C*(eps*referenceRadius delta Rstar p L y) := by
  obtain ⟨CH,hCH,HCH⟩ := exists_current_normalized_principal_operator_jet_bound
  obtain ⟨K,hK,HK⟩ := exists_reference_principal_operator_first_jet_bound S L
  have hKpos : 0 < K := by linarith
  let q : ℝ := 9*K^5+6*K^4+9*K^3+6*K^2
  have hq : 0 < q := by dsimp [q];positivity
  let t : ℝ := min 1 (1/(2*K))/CH
  have ht : 0 < t := div_pos (lt_min (by norm_num) (div_pos (by norm_num) (by positivity))) hCH
  refine ⟨q*CH,t,mul_pos hq hCH,ht,?_⟩
  intro lam hlam delta Rstar eps p hBoot y hy hSmallr G M
  let A := metricOperatorField (referenceNormalizedPrincipalMatrix S.g1 S.g2 L lam)
  let A0 := fun Y => Ring.inverse (G Y)
  let H := metricOperatorField (referenceNormalizedPrincipalDifference S.g1 S.g2 L lam)
  let d : ℝ := CH*(eps*referenceRadius delta Rstar p L y)
  have hGdata := conformalReference_slice_data S.g1 S.g1_admissible L lam
  have hA : ContDiff ℝ ∞ A := contDiff_actual_normalized_principal_operator S L lam
  have hA0 : ContDiff ℝ ∞ A0 := hGdata.2.1
  have hUnit (Y : R3) : IsUnit (A Y) := isUnit_normalized_principal_operator S L lam Y
  have hUnitG (Y : R3) : IsUnit (G Y) :=
    isUnit_of_strictly_positive _ (conformalReferenceOperatorJoint_pos S.g1 S.g1_admissible L (lam,Y))
  have hUnit0 (Y : R3) : IsUnit (A0 Y) := by
    obtain ⟨u,hu⟩ := hUnitG Y
    change IsUnit (Ring.inverse (G Y))
    rw [← hu,Ring.inverse_unit]
    exact Units.isUnit _
  have hInv0 : (fun Y => Ring.inverse (A0 Y))=G :=
    funext (fun Y => ring_inverse_inverse_of_isUnit (G Y) (hUnitG Y))
  have hM : M=(fun Y => Ring.inverse (A Y)) :=
    funext (actual_covariant_second_operator_eq_ringInverse S L lam)
  have hFields : (fun Y => A Y-A0 Y)=H :=
    funext (normalized_principal_operator_difference_eq S L lam)
  obtain ⟨hG,hA0value,hDA0⟩ := HK lam hlam y hy
  obtain ⟨hH,hDH⟩ := HCH S L lam delta Rstar eps p hBoot y hy
  have hValue : ‖A y-A0 y‖ ≤ d := by
    change ‖(fun Y => A Y-A0 Y) y‖ ≤ d
    rw [hFields]
    exact hH
  have hJet : ‖fderiv ℝ A y-fderiv ℝ A0 y‖ ≤ d := by
    rw [← fderiv_fun_sub (hA.differentiable (by simp) y) (hA0.differentiable (by simp) y),hFields]
    exact hDH
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hValue
  have hdmin : d ≤ min 1 (1/(2*K)) := by
    have hs := (le_div_iff₀ hCH).mp hSmallr
    simpa only [d,mul_comm] using hs
  have hd1 : d ≤ 1 := hdmin.trans (min_le_left _ _)
  have hKd : K*d ≤ 1/2 := by
    have hs := (le_div_iff₀ (by positivity : 0 < 2*K)).mp (hdmin.trans (min_le_right _ _))
    nlinarith only [hs]
  have hInvValue : ‖Ring.inverse (A0 y)‖ ≤ K := by rw [show Ring.inverse (A0 y)=G y from congrFun hInv0 y];exact hG
  obtain ⟨hDM,hDeltaDM⟩ := inverse_first_jet_perturbation_bounds A A0 y
    (hA.differentiable (by simp) y) (hA0.differentiable (by simp) y)
    (hUnit y) (hUnit0 y) K d hKpos.le hInvValue hDA0 hValue hJet hd1 hKd
  rw [hInv0] at hDeltaDM
  have hQactual : inverseMetricField M y=A y :=
    inverse_actual_covariant_second_operator_eq_principal S L lam y
  change ‖coordinateConnectionLinearMap (inverseMetricField M y) (fderiv ℝ M y)-
      coordinateConnectionLinearMap (A0 y) (fderiv ℝ G y)‖ ≤ _
  rw [hQactual,hM]
  have hConn := norm_coordinateConnectionLinearMap_sub_le (A y) (A0 y)
    (fderiv ℝ (fun Y => Ring.inverse (A Y)) y) (fderiv ℝ G y)
  calc
    _ ≤ (3/2 : ℝ)*(‖A y-A0 y‖*‖fderiv ℝ (fun Y => Ring.inverse (A Y)) y‖+
        ‖A0 y‖*‖fderiv ℝ (fun Y => Ring.inverse (A Y)) y-fderiv ℝ G y‖) := hConn
    _ ≤ (3/2 : ℝ)*(d*(4*K^2*(K+1))+K*((6*K^4+4*K^3+2*K^2)*d)) := by gcongr
    _ = (q*CH)*(eps*referenceRadius delta Rstar p L y) := by dsimp [q,d];ring

/-- The original radius bootstrap discharges the local smallness condition. -/
theorem eps_mul_radius_small_of_original_bootstrap
    (r beta eps t : ℝ) (hr : 0 ≤ r) (hb : 1 ≤ beta)
    (hBoot : r*beta^2 ≤ eps) (heps : eps ≤ min 1 t) : eps*r ≤ t := by
  have hb2 : 1 ≤ beta^2 := by nlinarith
  have hre : r ≤ eps := (by nlinarith [mul_le_mul_of_nonneg_left hb2 hr] : r ≤ r*beta^2).trans hBoot
  have he0 : 0 ≤ eps := hr.trans hre
  have hr1 : r ≤ 1 := hre.trans (heps.trans (min_le_left _ _))
  exact (mul_le_mul_of_nonneg_left hr1 he0).trans (by simpa only [mul_one] using heps.trans (min_le_right _ _))

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
