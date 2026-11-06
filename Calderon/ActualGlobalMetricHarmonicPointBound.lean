import Calderon.ActualRadiusTwoScaledMetricGreenBound
import Calderon.CollaboratorUCPLocalOct17
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric TopologicalSpace Filter
open scoped ENNReal ContDiff Distributions Topology InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily MetricVolume
open Literature (nativeMetricDifferential)

theorem exists_rescaled_euclidean_harmonic_point_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : R3),
      ∀ (r : ℝ), 0 < r →
      ∀ H : R3 → ℝ, ContDiffOn ℝ ∞ H (ball q r) →
      MemLp H 2 ((volume : Measure R3).restrict (ball q r)) →
      (∀ x ∈ ball q r, divCoeffGrad (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) H x = 0) →
      |H q| ≤ C*r^(-(3 : ℝ)/2)*Real.sqrt (∫ x in ball q r, H x^2) := by
  obtain ⟨Cu,hCu,hUnit⟩ := exists_uniform_radiusTwoScaledMetric_harmonic_point_bound hreg hcalc g hg
  refine ⟨Real.sqrt 8*Cu,by positivity,?_⟩
  intro q r hr H hH hMem hPDE
  let rho : ℝ := r/2
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrhoLe : rho ≤ r := by dsimp only [rho]; linarith only [hr]
  let U : R3 → ℝ := fun z => H (q+rho • z)
  have hMaps (z : R3) (hz : z ∈ ball (0 : R3) 2) : q+rho • z ∈ ball q r := by
    change dist (q+rho • z) q < r
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hrho]
    have hn := mem_ball_zero_iff.mp hz
    dsimp only [rho]
    nlinarith only [hn,hr]
  have hAffineCDF : ContDiff ℝ ∞ (fun z : R3 => q+rho • z) :=
    (contDiff_const (c := q)).add (contDiff_const_smul rho)
  have hU : ContDiffOn ℝ ∞ U (ball (0 : R3) 2) :=
    hH.comp hAffineCDF.contDiffOn hMaps
  have hEq (x : R3) (hx : x ∈ (ballOpens : Set R3)) :
      divCoeffGrad (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ)) U x = 0 := by
    have hx2 : x ∈ ball (0:R3) 2 := (ball_subset_ball (by norm_num : (1:ℝ)≤2)) hx
    have hOld := hPDE (q+rho • x) (hMaps x hx2)
    have hAffinePDE := Regularity.Jets.divCoeffGrad_comp_affine
      (fun _ : R3 => (1:Matrix (Fin 3) (Fin 3) ℝ)) H q hrho.ne' x
    exact hAffinePDE.trans (by rw [hOld,mul_zero])
  let e2 : R3 := EuclideanSpace.single (2:Fin 3) (1:ℝ)
  have he2 : ‖e2‖ = 1 := by simp [e2]
  have hIdentity : principalCoefficient g e2 = 1 :=
    principalCoefficient_eq_one_of_exterior g hg e2 (by rw [he2])
  have ht : (e2,(0:ℝ)) ∈ closedBall (0:R3) (5/4:ℝ) ×ˢ Icc (0:ℝ) (1/4:ℝ) := by
    refine ⟨?_,by norm_num,by norm_num⟩
    simpa only [mem_closedBall,dist_zero_right,he2] using (by norm_num : (1:ℝ)≤5/4)
  have hEqActual (x : R3) (hx : x ∈ (ballOpens:Set R3)) :
      divCoeffGrad (fun z => principalCoefficient g (e2+(0:ℝ) • z)) U x = 0 := by
    simpa only [zero_smul,add_zero,hIdentity] using hEq x hx
  have hPoint := hUnit (e2,0) ht U hU hEqActual
  have hAff : Affine.IsAff (Affine.ballO q rho) ballOpens q rho := by
    intro z
    change dist (q+rho • z) q < rho ↔ dist z 0 < 1
    simp only [dist_eq_norm,add_sub_cancel_left,sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos hrho]
    constructor <;> intro h <;> nlinarith only [h,hrho]
  have hChange : rho^3*(∫ x in (ballOpens : Set R3), U x^2) =
      ∫ x in ball q rho, H x^2 := by
    have hc := (Affine.mp_restrict hrho hAff).integral_comp
      (Affine.measurableEmbedding_aff q hrho) (fun x => H x^2)
    rw [integral_smul_measure] at hc
    simpa only [U,Affine.aff,Affine.ballO,Opens.coe_mk,Affine.sc,
      ENNReal.toReal_ofReal (pow_nonneg hrho.le 3),smul_eq_mul] using hc
  have hILe : (∫ x in ball q rho, H x^2) ≤ ∫ x in ball q r, H x^2 :=
    setIntegral_mono_set hMem.integrable_sq (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ hx => (ball_subset_ball hrhoLe) hx)
  have hFactor : rho^3*(8*(r^3)⁻¹) = 1 := by
    dsimp only [rho]
    field_simp [hr.ne']
    <;> ring
  have hScaled : (∫ x in (ballOpens : Set R3), U x^2) ≤
      (8*(r^3)⁻¹)*(∫ x in ball q r, H x^2) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hrho 3)).mp
    calc
      _ = ∫ x in ball q rho, H x^2 := hChange
      _ ≤ ∫ x in ball q r, H x^2 := hILe
      _ = rho^3*((8*(r^3)⁻¹)*(∫ x in ball q r, H x^2)) := by
        rw [← mul_assoc,hFactor,one_mul]
  have hPower : (r^(-(3 : ℝ)/2))^2 = (r^3)⁻¹ := by
    calc
      (r^(-(3 : ℝ)/2))^2 = r^(-(3 : ℝ)) := by
        rw [← Real.rpow_natCast _ 2,← Real.rpow_mul hr.le]
        congr 1
        norm_num
      _ = (r^(3 : ℝ))⁻¹ := Real.rpow_neg hr.le 3
      _ = (r^3)⁻¹ := congrArg Inv.inv (Real.rpow_natCast r 3)
  have hI : 0 ≤ ∫ x in ball q r, H x^2 := integral_nonneg fun _ => sq_nonneg _
  have hSqrt : Real.sqrt (∫ x in (ballOpens : Set R3), U x^2) ≤
      Real.sqrt 8*r^(-(3 : ℝ)/2)*Real.sqrt (∫ x in ball q r, H x^2) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),mul_pow,mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),hPower,Real.sq_sqrt hI]
    exact hScaled
  have hZero : U (0 : R3) = H q := by simp only [U,smul_zero,add_zero]
  rw [hZero] at hPoint
  exact hPoint.trans ((mul_le_mul_of_nonneg_left hSqrt hCu.le).trans_eq (by ring))

theorem exists_uniform_admissibleMetric_global_rescaled_harmonic_point_bound
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : R3) (r : ℝ), 0 < r → r ≤ (1/8:ℝ) →
      ∀ H : R3 → ℝ, ContDiffOn ℝ ∞ H (ball q r) →
      MemLp H 2 ((volume:Measure R3).restrict (ball q r)) →
      (∀ x ∈ ball q r, nativeMetricDifferential g H x = 0) →
      |H q| ≤ C*r^(-(3:ℝ)/2)*Real.sqrt (∫ x in ball q r, H x^2) := by
  obtain ⟨Cg,hCg,hG⟩ := exists_uniform_radiusTwo_rescaled_nativeHarmonic_point_bound hreg hcalc g hg
  obtain ⟨Ce,hCe,hE⟩ := exists_rescaled_euclidean_harmonic_point_bound hreg hcalc g hg
  refine ⟨max Cg Ce,hCg.trans_le (le_max_left _ _),?_⟩
  intro q r hr hrMax H hH hMem hPDE
  have hCap : |H q| ≤ max Cg Ce*r^(-(3:ℝ)/2)*Real.sqrt (∫ x in ball q r, H x^2) := by
    by_cases hq : ‖q‖ ≤ (5/4:ℝ)
    · have h := hG q (mem_closedBall_zero_iff.mpr hq) r hr (by linarith) H hH hMem hPDE
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)) (Real.sqrt_nonneg _))
    · have hqGt : (5/4:ℝ) < ‖q‖ := lt_of_not_ge hq
      have hCoeff : ∀ x ∈ ball q r, principalCoefficient g x = 1 := by
        intro x hx
        apply principalCoefficient_eq_one_of_exterior g hg x
        have hxq : ‖x-q‖ < r := by simpa only [mem_ball,dist_eq_norm] using hx
        have hTri := norm_add_le (q-x) x
        rw [sub_add_cancel] at hTri
        rw [norm_sub_rev] at hTri
        linarith
      have hEuclidean : ∀ x ∈ ball q r, divCoeffGrad (fun _ : R3 => (1:Matrix (Fin 3) (Fin 3) ℝ)) H x = 0 := by
        intro x hx
        have hNear : principalCoefficient g =ᶠ[𝓝 x] (fun _ : R3 => (1:Matrix (Fin 3) (Fin 3) ℝ)) := by
          filter_upwards [isOpen_ball.mem_nhds hx] with z hz
          exact hCoeff z hz
        have hEq := UCP.divCoeffGrad_congr hNear (Filter.EventuallyEq.refl (𝓝 x) H)
        have hOld := hPDE x hx
        change -divCoeffGrad (principalCoefficient g) H x = 0 at hOld
        exact hEq.symm.trans (neg_eq_zero.mp hOld)
      exact (hE q r hr H hH hMem hEuclidean).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)) (Real.sqrt_nonneg _))
  exact hCap

end OAI.AnisotropicCalderon.ExteriorSource
