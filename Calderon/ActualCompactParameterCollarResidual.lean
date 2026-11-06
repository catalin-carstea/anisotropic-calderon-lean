import Calderon.ActualCompactParameterCutoffResidual
import Calderon.ActualCompactParameterCaccioppoli
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_joint_collar_residual_l2_bound
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a:E→Fin 3→Fin 3→R3→ℝ) (ha:∀ i j,JointSmooth fun P => a P i j)
    (hs:∀ P i j x,a P i j x=a P j i x) (A:Set E) (hA:IsCompact A)
    {D U K:Set R3} (hD:IsOpen D) (hU:IsOpen U) (hUD:U⊆D)
    (hK:IsCompact K) (hKU:K⊆U)
    (hpos:∀ P∈A,∀ x∈U,∀ xi:Fin 3→ℝ,xi≠0 → 0 < ∑ i,∑ k,xi i*a P i k x*xi k)
    {chi beta:R3→ℝ} (hchi:ContDiff ℝ ∞ chi) (hchic:HasCompactSupport chi)
    (htc:tsupport chi⊆D) (hbeta:Continuous beta) :
    ∃ C:ℝ,0 ≤ C ∧ ∀ P∈A,∀ w:R3→ℝ,ContDiffOn ℝ ∞ w D →
      (∀ x∈D,Lop (a P) w x=0) → IntegrableOn (fun x => w x^2) U →
      ∫ x in K,(beta x*Lop (a P) (fun y => chi y*w y) x)^2 ≤ C*∫ x in U,w x^2 := by
  obtain ⟨C1,hC1,hpt⟩ := exists_joint_compact_cutoff_residual_pointwise_bound_local a ha hs A hA
    hD hK (hKU.trans hUD) hchi hchic htc hbeta
  obtain ⟨C2,hC2,hcac⟩ := joint_collar_caccioppoli a ha A hA hU hK hKU hpos
  obtain ⟨zeta,hzeta,-,hzD,hz1⟩ := CutoffCommutator.exists_plateau_cutoff hD hK (hKU.trans hUD)
  refine ⟨C1*(1+C2),by positivity,?_⟩
  intro P hP w hw hLw hwint
  have hW : ContDiff ℝ ∞ (fun y => zeta y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hzeta hzD hw
  have hgerm : ∀ y ∈ K, (fun y => zeta y * w y) =ᶠ[𝓝 y] w := fun y hy => by
    filter_upwards [hz1 y hy] with z hz
    rw [hz, one_mul]
  have hwK : ContinuousOn w K := hw.continuousOn.mono (hKU.trans hUD)
  have hpdK : ∀ j, ContinuousOn (fun x => pd j w x) K := fun j =>
    (OAI.AnisotropicCalderon.contDiff_pd_apply hW).continuous.continuousOn.congr
      fun x hx => (pd_congr_of_eventuallyEq (hgerm x hx) j).symm
  have hiw : IntegrableOn (fun x => w x ^ 2) K := (hwK.pow 2).integrableOn_compact hK
  have higrad : IntegrableOn (fun x => ∑ j, pd j w x ^ 2) K :=
    (continuousOn_finset_sum _ fun j _ => (hpdK j).pow 2).integrableOn_compact hK
  have hcw : ContDiff ℝ ∞ (fun y => chi y * w y) :=
    OAI.AnisotropicCalderon.CutoffCommutator.contDiff_mul_of_tsupport_subset hD hchi htc hw
  have hLop : Continuous (Lop (a P) (fun y => chi y * w y)) := by
    unfold Lop
    exact continuous_finsetSum _ fun i _ => (OAI.AnisotropicCalderon.contDiff_pd_apply
      (ContDiff.sum fun k _ => (jointSmooth_slice (ha i k) P).mul
        (OAI.AnisotropicCalderon.contDiff_pd_apply hcw))).continuous
  have hres : IntegrableOn (fun x => (beta x * Lop (a P) (fun y => chi y * w y) x) ^ 2) K :=
    ((hbeta.mul hLop).pow 2).continuousOn.integrableOn_compact hK
  have h1 : ∫ x in K, (beta x * Lop (a P) (fun y => chi y * w y) x) ^ 2 ≤
      ∫ x in K, C1 * (w x ^ 2 + ∑ j, pd j w x ^ 2) :=
    setIntegral_mono_on hres ((hiw.add higrad).const_mul C1) hK.measurableSet
      (fun x hx => hpt P hP w hw hLw x hx)
  rw [integral_const_mul, integral_add hiw higrad] at h1
  have h2 : ∫ x in K, w x ^ 2 ≤ ∫ x in U, w x ^ 2 :=
    setIntegral_mono_set hwint
      (Filter.Eventually.of_forall fun x => show (0 : ℝ) ≤ w x ^ 2 from sq_nonneg _)
      hKU.eventuallyLE
  have h3 := hcac P hP w (hw.mono hUD) (fun x hx => hLw x (hUD hx)) hwint
  calc ∫ x in K, (beta x * Lop (a P) (fun y => chi y * w y) x) ^ 2
      ≤ C1 * ((∫ x in K, w x ^ 2) + (∫ x in K, ∑ j, pd j w x ^ 2)) := h1
    _ ≤ C1 * ((∫ x in U, w x ^ 2) + C2 * (∫ x in U, w x ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) hC1
    _ = C1 * (1 + C2) * (∫ x in U, w x ^ 2) := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
