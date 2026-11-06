import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace OAI.AnisotropicCalderon.ConnectionError

universe u
variable {P V : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual derivative in the parameter, with the integration variable fixed. -/
def parameterUnitIntervalDerivative (H : P × ℝ → V) (a : P × ℝ) : P →L[ℝ] V :=
  (fderiv ℝ H a).comp (ContinuousLinearMap.inl ℝ P ℝ)

/-- Compactness of the integration interval gives a single parameter neighborhood bound. -/
theorem exists_local_uniform_unitInterval_bound (H : P × ℝ → V)
    (hH : Continuous H) (p0 : P) :
    ∃ (U : Set P) (C : ℝ), U ∈ 𝓝 p0 ∧ 0 ≤ C ∧
      ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ‖H (p,t)‖ ≤ C := by
  have hc : Continuous (fun t : ℝ => H (p0,t)) :=
    hH.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C0,hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  let C : ℝ := max C0 0 + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ho : IsOpen {a : P × ℝ | ‖H a‖ < C} :=
    isOpen_lt hH.norm continuous_const
  have hsub : ({p0} : Set P) ×ˢ Icc (0 : ℝ) 1 ⊆ {a : P × ℝ | ‖H a‖ < C} := by
    intro a ha
    have hp : a.1 = p0 := mem_singleton_iff.mp ha.1
    change ‖H (a.1,a.2)‖ < C
    rw [hp]
    have hb := hC0 a.2 ha.2
    dsimp [C]
    linarith [le_max_left C0 0]
  obtain ⟨U,W,hU,_,h0U,hTW,hUW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc ho hsub
  refine ⟨U,C,hU.mem_nhds (h0U (mem_singleton p0)),hC,?_⟩
  intro p hp t ht
  exact (hUW (a := (p,t)) ⟨hp,hTW ht⟩).le

theorem contDiff_parameterUnitIntervalDerivative (H : P × ℝ → V)
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (parameterUnitIntervalDerivative H) :=
  (hH.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const

theorem hasFDerivAt_parameterUnitInterval_slice (H : P × ℝ → V)
    (hH : ContDiff ℝ ∞ H) (p : P) (t : ℝ) :
    HasFDerivAt (fun x => H (x,t)) (parameterUnitIntervalDerivative H (p,t)) p :=
  ((hH.differentiable (by simp) (p,t)).hasFDerivAt.comp p
    (hasFDerivAt_prodMk_left p t))

variable [CompleteSpace V]

/-- Every domination and measurability hypothesis is supplied by the actual joint derivative. -/
theorem hasFDerivAt_parameter_unitInterval_integral (H : P × ℝ → V)
    (hH : ContDiff ℝ ∞ H) (p : P) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, H (x,t))
      (∫ t in (0 : ℝ)..1, parameterUnitIntervalDerivative H (p,t)) p := by
  let J : P × ℝ → P →L[ℝ] V := parameterUnitIntervalDerivative H
  have hJ : ContDiff ℝ ∞ J := contDiff_parameterUnitIntervalDerivative H hH
  obtain ⟨U,C,hU,_,hbound⟩ := exists_local_uniform_unitInterval_bound J hJ.continuous p
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => H (x,t)) (F' := fun x t => J (x,t))
    (s := U) (bound := fun _ : ℝ => C) hU
  · filter_upwards with x
    exact (hH.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hH.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  · exact (hJ.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards with t ht x hx
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    exact hbound x hx t ⟨ht'.1.le,ht'.2⟩
  · exact intervalIntegrable_const
  · filter_upwards with t _ x _
    exact hasFDerivAt_parameterUnitInterval_slice H hH x t

/-- The codomain is generalized in the finite-order induction, including CLM codomains. -/
theorem contDiff_nat_parameter_unitInterval_integral (H : P × ℝ → V)
    (hH : ContDiff ℝ ∞ H) (n : ℕ) :
    ContDiff ℝ n (fun p => ∫ t in (0 : ℝ)..1, H (p,t)) := by
  induction n generalizing V with
  | zero =>
    apply contDiff_zero.mpr
    have hd : Differentiable ℝ (fun p => ∫ t in (0 : ℝ)..1, H (p,t)) :=
      fun p => (hasFDerivAt_parameter_unitInterval_integral H hH p).differentiableAt
    exact hd.continuous
  | succ n ih =>
    let J : P × ℝ → P →L[ℝ] V := parameterUnitIntervalDerivative H
    have hJ : ContDiff ℝ ∞ J := contDiff_parameterUnitIntervalDerivative H hH
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun p => ∫ t in (0 : ℝ)..1, J (p,t),ih J hJ,?_⟩
    intro p
    exact hasFDerivAt_parameter_unitInterval_integral H hH p

theorem contDiff_parameter_unitInterval_integral (H : P × ℝ → V)
    (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, H (p,t)) := by
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  exact contDiff_nat_parameter_unitInterval_integral H hH n

/-- The radial derivative is the true joint derivative evaluated in the radial direction. -/
def parameterRadialDerivative (F : P × ℝ → V) (a : P × ℝ) : V :=
  fderiv ℝ F a (0,1)

/-- Smooth signed-radius division is an average of the actual radial derivative. -/
def parameterHadamardDivision (F : P × ℝ → V) (a : P × ℝ) : V :=
  ∫ t in (0 : ℝ)..1, parameterRadialDerivative F (a.1,t*a.2)

theorem contDiff_parameterRadialDerivative (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (parameterRadialDerivative F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasDerivAt_parameter_radial_slice (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ) :
    HasDerivAt (fun s => F (p,s)) (parameterRadialDerivative F (p,r)) r := by
  exact (hF.differentiable (by simp) (p,r)).hasFDerivAt.comp_hasDerivAt r
    ((hasDerivAt_const r p).prodMk (hasDerivAt_id r))

theorem contDiff_parameterHadamardDivision (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (parameterHadamardDivision F) := by
  let H : (P × ℝ) × ℝ → V := fun a => parameterRadialDerivative F (a.1.1,a.2*a.1.2)
  have hH : ContDiff ℝ ∞ H := (contDiff_parameterRadialDerivative F hF).comp
    (contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd))
  exact contDiff_parameter_unitInterval_integral H hH

theorem parameterHadamardDivision_zero (F : P × ℝ → V) (p : P) :
    parameterHadamardDivision F (p,0) = parameterRadialDerivative F (p,0) := by
  simp only [parameterHadamardDivision,mul_zero,intervalIntegral.integral_const,
    sub_zero,one_smul]

theorem parameterHadamardDivision_zero_eq_deriv (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (p : P) :
    parameterHadamardDivision F (p,0) = deriv (fun r => F (p,r)) 0 := by
  rw [parameterHadamardDivision_zero]
  exact (hasDerivAt_parameter_radial_slice F hF p 0).deriv.symm

theorem radius_smul_parameterHadamardDivision (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ) :
    r • parameterHadamardDivision F (p,r) = F (p,r) - F (p,0) := by
  have hc : ContinuousOn (fun t : ℝ => parameterRadialDerivative F (p,t*r))
      (Icc (0 : ℝ) 1) :=
    ((contDiff_parameterRadialDerivative F hF).continuous.comp
      (continuous_const.prodMk (continuous_id.mul continuous_const))).continuousOn
  simpa only [parameterHadamardDivision,zero_add,smul_eq_mul,add_zero] using
    (intervalIntegral.integral_unitInterval_deriv_eq_sub
      (f := fun s : ℝ => F (p,s)) (f' := fun s => parameterRadialDerivative F (p,s))
      (z₀ := (0 : ℝ)) (z₁ := r)
      (by simpa only [zero_add,smul_eq_mul] using hc)
      (fun t _ => hasDerivAt_parameter_radial_slice F hF p (0+t • r)))

theorem parameterHadamardDivision_eq_inv_smul (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ)
    (hzero : F (p,0) = 0) (hr : r ≠ 0) :
    parameterHadamardDivision F (p,r) = r⁻¹ • F (p,r) := by
  have hf : r • parameterHadamardDivision F (p,r) = F (p,r) := by
    simpa only [hzero,sub_zero] using radius_smul_parameterHadamardDivision F hF p r
  rw [← hf,smul_smul,inv_mul_cancel₀ hr,one_smul]

theorem exists_smooth_parameter_radial_division (F : P × ℝ → V)
    (hF : ContDiff ℝ ∞ F) (hzero : ∀ p, F (p,0) = 0) :
    ∃ G : P × ℝ → V, ContDiff ℝ ∞ G ∧
      (∀ p r, F (p,r) = r • G (p,r)) ∧
      ∀ p, G (p,0) = deriv (fun r => F (p,r)) 0 := by
  refine ⟨parameterHadamardDivision F,contDiff_parameterHadamardDivision F hF,?_,
    parameterHadamardDivision_zero_eq_deriv F hF⟩
  intro p r
  simpa only [hzero p,sub_zero] using (radius_smul_parameterHadamardDivision F hF p r).symm

end OAI.AnisotropicCalderon.ConnectionError
