import MixedKernelNativeProductAndBasis
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open Set Metric Filter
open scoped ContDiff Topology

/-- Every neighborhood of a noncritical scalar zero contains an actual negative point. -/
theorem exists_negative_mem_open_of_fderiv_ne_zero
    (psi : R3 → ℝ) (p : R3) (hpsi : ContDiffAt ℝ 2 psi p)
    (hzero : psi p = 0) (hne : fderiv ℝ psi p ≠ 0)
    {U : Set R3} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ x ∈ U, psi x < 0 := by
  classical
  have hv : ∃ v : R3, fderiv ℝ psi p v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext v
    exact h v
  obtain ⟨v,hv⟩ := hv
  let c : ℝ → R3 := fun t => p+t • v
  let f : ℝ → ℝ := fun t => psi (c t)
  have hc0 : c 0 = p := by simp [c]
  have hc : ContDiff ℝ 2 c := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hderc : HasDerivAt c v 0 := by
    have h := (hasDerivAt_const (0 : ℝ) p).add ((hasDerivAt_id (0 : ℝ)).smul_const v)
    change HasDerivAt (fun t : ℝ => p + t • v) ((0 : R3) + (1 : ℝ) • v) 0 at h
    simpa only [zero_add,one_smul] using h
  have hpsic : ContDiffAt ℝ 2 psi (c 0) := by rw [hc0]; exact hpsi
  have hcf : ContDiffAt ℝ 2 f 0 := hpsic.comp 0 hc.contDiffAt
  have hDf : HasDerivAt f (fderiv ℝ psi p v) 0 := by
    have hd : HasFDerivAt psi (fderiv ℝ psi p) (c 0) := by
      rw [hc0]
      exact (hpsi.differentiableAt (by norm_num)).hasFDerivAt
    exact hd.comp_hasDerivAt 0 hderc
  have hstrict : HasStrictDerivAt f (fderiv ℝ psi p v) 0 :=
    hcf.hasStrictDerivAt' hDf (by norm_num)
  have hf0 : f 0 = 0 := by simpa only [f,hc0] using hzero
  let V : Set ℝ := c ⁻¹' U
  have hV : V ∈ 𝓝 (0 : ℝ) :=
    hc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds (by rw [hc0]; exact hp))
  have hIm : f '' V ∈ 𝓝 (0 : ℝ) := by
    rw [← hf0,← hstrict.map_nhds_eq hv]
    exact Filter.image_mem_map hV
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hIm
  have hneg : -r/2 ∈ ball (0 : ℝ) r := by
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_neg (by linarith)]
    linarith
  obtain ⟨t,ht,hft⟩ := hball hneg
  refine ⟨c t,ht,?_⟩
  change f t < 0
  rw [hft]
  linarith

/-- The SAME original W meets every open neighborhood of each sufficiently local actual separator point. -/
theorem known_side_meets_open_at_separator (S : KnownSideSourceData) :
    ∃ a : ℝ, 0 < a ∧ ∀ lam : ℝ, 0 < lam → ∀ p : R3,
      lam • p ∈ ball (0 : R3) a → S.separating_function (lam • p) = 0 →
      ∀ U : Set R3, IsOpen U → p ∈ U → ∃ x ∈ U, lam • x ∈ S.W := by
  obtain ⟨a,ha,hball,hW,hnc⟩ := separating_noncritical_ball S
  refine ⟨a,ha,fun lam hlam p hp hp0 U hU hpU => ?_⟩
  let psi : R3 → ℝ := fun x => S.separating_function (lam • x)
  have hcd : ContDiffAt ℝ ∞ S.separating_function (lam • p) :=
    S.separating_function_smooth.contDiffAt (S.coordinateRoom_open.mem_nhds (hball hp))
  have hpsi : ContDiffAt ℝ 2 psi p :=
    (hcd.comp p (contDiffAt_id.const_smul lam)).of_le (by simp)
  have hD : HasFDerivAt psi
      ((fderiv ℝ S.separating_function (lam • p)).comp
        (lam • ContinuousLinearMap.id ℝ R3)) p :=
    (hcd.differentiableAt (by simp)).hasFDerivAt.comp p
      ((hasFDerivAt_id p).const_smul lam)
  have hne : fderiv ℝ psi p ≠ 0 := by
    intro h
    apply hnc _ hp
    ext v
    have hh : ((fderiv ℝ S.separating_function (lam • p)).comp
        (lam • ContinuousLinearMap.id ℝ R3)) v = 0 := by
      rw [← hD.fderiv,h]
      rfl
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,map_smul,smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left hlam.ne'
  let U0 : Set R3 := U ∩ {x | lam • x ∈ ball (0 : R3) a}
  have hU0 : IsOpen U0 := hU.inter (isOpen_ball.preimage (continuous_id.const_smul lam))
  obtain ⟨x,hx,hxneg⟩ := exists_negative_mem_open_of_fderiv_ne_zero psi p hpsi hp0 hne hU0 ⟨hpU,hp⟩
  exact ⟨x,hx.1,hW ⟨hx.2,hxneg⟩⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
