import Calderon.ActualCompactParameterEllipticity
import MixedKernelClosedUniformFoundation
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_joint_caccioppoli_constant
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E→Fin 3→Fin 3→R3→ℝ) (ha : ∀ i k,JointSmooth fun P => a P i k)
    (A : Set E) (hA : IsCompact A) {eta : R3→ℝ} (heta : ContDiff ℝ ∞ eta)
    (hetac : HasCompactSupport eta)
    (hpos : ∀ P∈A,∀ x∈tsupport eta,∀ xi:Fin 3→ℝ,xi≠0 →
      0 < ∑ i,∑ k,xi i*a P i k x*xi k) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ P∈A,∀ u:R3→ℝ,ContDiff ℝ ∞ u →
      (∀ x,eta x≠0 → Lop (a P) u x=0) →
      ∫ x,eta x^2*∑ i,pd i u x^2 ≤ C*∫ x,u x^2*∑ i,pd i eta x^2 := by
  obtain ⟨lamE,Lambda,hl,hlow,hup⟩ := CutoffCommutator.ellipticity_on_compact_parameter_space
    (a:=fun i k (z:E×R3) => a z.1 i k z.2) (fun i k => (ha i k).continuous)
    (hA.prod hetac) (fun z hz xi hxi => hpos z.1 hz.1 z.2 hz.2 xi hxi)
  refine ⟨(2*Lambda/lamE)^2,sq_nonneg _,?_⟩
  intro P hP u hu hL
  exact CutoffCommutator.caccioppoli_of_ellipticity
    (fun i k => jointSmooth_slice (ha i k) P) heta hetac hu hL hl
    (fun x hx => hlow (P,x) ⟨hP,subset_tsupport eta hx⟩)
    (fun x hx => hup (P,x) ⟨hP,subset_tsupport eta hx⟩)

theorem joint_collar_caccioppoli
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E→Fin 3→Fin 3→R3→ℝ) (ha : ∀ i k,JointSmooth fun P => a P i k)
    (A : Set E) (hA : IsCompact A)
    {U K:Set R3} (hU:IsOpen U) (hK:IsCompact K) (hKU:K⊆U)
    (hpos:∀ P∈A,∀ x∈U,∀ xi:Fin 3→ℝ,xi≠0 → 0 < ∑ i,∑ k,xi i*a P i k x*xi k) :
    ∃ C:ℝ,0 ≤ C ∧ ∀ P∈A,∀ w:R3→ℝ,ContDiffOn ℝ ∞ w U →
      (∀ x∈U,Lop (a P) w x=0) → IntegrableOn (fun x => w x^2) U →
      ∫ x in K,∑ i,pd i w x^2 ≤ C*∫ x in U,w x^2 := by
  obtain ⟨eta,heta,hetac,hetaU,heta1⟩ := CutoffCommutator.exists_plateau_cutoff hU hK hKU
  obtain ⟨zeta,hzeta,-,hzetaU,hzeta1⟩ := CutoffCommutator.exists_plateau_cutoff hU hetac hetaU
  obtain ⟨C0,hC0,hcac⟩ := exists_joint_caccioppoli_constant a ha A hA heta hetac
    (fun P hP x hx => hpos P hP x (hetaU hx))
  have hgcont : Continuous (fun x => ∑ i,pd i eta x^2) :=
    continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply heta).continuous.pow 2
  obtain ⟨M0,hM0⟩ := (show IsCompact (tsupport eta) from hetac).exists_bound_of_continuousOn hgcont.continuousOn
  have hM : 0 ≤ max M0 0 := le_max_right _ _
  refine ⟨C0*max M0 0,mul_nonneg hC0 hM,?_⟩
  intro P hP w hw hLw hwint
  have hu : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hU hzeta hzetaU hw
  have heq : ∀ x ∈ tsupport eta, (fun y => zeta y * w y) =ᶠ[nhds x] w := fun x hx => by
    filter_upwards [hzeta1 x hx] with y hy
    rw [hy, one_mul]
  have hL : ∀ x, eta x ≠ 0 → Lop (a P) (fun y => zeta y * w y) x = 0 := fun x hx => by
    rw [Lop_congr_of_eventuallyEq (a P) (heq x (subset_tsupport eta hx))]
    exact hLw x (hetaU (subset_tsupport eta hx))
  have hc := hcac P hP _ hu hL
  beta_reduce at hc
  have hpd0 : ∀ x, x ∉ tsupport eta → ∑ i, pd i eta x ^ 2 = 0 := fun x hx => by
    have h0 : ∀ i, pd i eta x = 0 := fun i => by
      rw [pd_congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx) i]
      simp [pd]
    simp [h0]
  have hpt : ∀ x, (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2 ≤
      max M0 0 * U.indicator (fun x => w x ^ 2) x := by
    intro x
    by_cases hx : x ∈ tsupport eta
    · have hz : zeta x = 1 := (hzeta1 x hx).eq_of_nhds
      rw [Set.indicator_of_mem (hetaU hx), hz, one_mul, mul_comm]
      have hb : ∑ i, pd i eta x ^ 2 ≤ max M0 0 := by
        have h1 := hM0 x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h1
        exact h1.trans (le_max_left _ _)
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    · rw [hpd0 x hx, mul_zero]
      exact mul_nonneg hM (Set.indicator_nonneg (fun _ _ => sq_nonneg _) x)
  have hint1 : Integrable (fun x => (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2) :=
    ((hu.continuous.pow 2).mul hgcont).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hetac fun x hx => by
        change (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2 = 0
        rw [hpd0 x hx, mul_zero])
  have hint2 : Integrable (fun x => max M0 0 * U.indicator (fun x => w x ^ 2) x) :=
    (hwint.integrable_indicator hU.measurableSet).const_mul _
  have hup : (∫ x, (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2) ≤
      max M0 0 * ∫ x in U, w x ^ 2 := by
    have hm := integral_mono hint1 hint2 hpt
    rw [integral_const_mul, integral_indicator hU.measurableSet] at hm
    exact hm
  have hgu : Integrable (fun x => eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2) :=
    OAI.AnisotropicCalderon.CutoffCommutator.integrable_of_eta_factor hetac
      ((heta.pow 2).mul (ContDiff.sum fun i _ =>
        (OAI.AnisotropicCalderon.contDiff_pd_apply hu).pow 2))
      (fun x h => by simp [h])
  have hKeq : ∫ x in K, ∑ i, pd i w x ^ 2 =
      ∫ x in K, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2 := by
    refine setIntegral_congr_fun hK.measurableSet fun x hx => ?_
    have he1 : eta x = 1 := (heta1 x hx).eq_of_nhds
    have hxt : x ∈ tsupport eta := subset_tsupport eta (by rw [Function.mem_support, he1]; norm_num)
    simp only [he1, one_pow, one_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [pd_congr_of_eventuallyEq (heq x hxt) i]
  have hKle : (∫ x in K, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2) ≤
      ∫ x, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2 :=
    setIntegral_le_integral hgu (Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  calc ∫ x in K, ∑ i, pd i w x ^ 2
      = ∫ x in K, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2 := hKeq
    _ ≤ ∫ x, eta x ^ 2 * ∑ i, pd i (fun y => zeta y * w y) x ^ 2 := hKle
    _ ≤ C0 * ∫ x, (zeta x * w x) ^ 2 * ∑ i, pd i eta x ^ 2 := hc
    _ ≤ C0 * (max M0 0 * ∫ x in U, w x ^ 2) := mul_le_mul_of_nonneg_left hup hC0
    _ = C0 * max M0 0 * ∫ x in U, w x ^ 2 := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
