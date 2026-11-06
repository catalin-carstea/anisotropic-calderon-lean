import Calderon.MixedKernelConstruction.MixedKernelPhaseStrictnessV021
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section

namespace OAI.AnisotropicCalderon.ProductHessianSeparation
open Set Metric Matrix Filter Topology
open scoped InnerProductSpace Matrix.Norms.Elementwise
local notation "V3" => (Fin 3 → ℝ)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ

/-- A continuous positive definite quadratic form has a positive minimum
on the norm-one sphere. Homogeneity bounds all points of the metric level set;
the covector equation and quadratic level equation are closed, hence their
bounded finite-dimensional intersection is compact. No nonzero normal/covector
or cone-duality premise is needed for this purely compactness statement. -/
theorem isCompact_metricTangentSphere (G : M3) (hG : G.PosDef) (ell a : V3) :
    IsCompact (metricTangentSphere G ell a) := by
  classical
  let A : ℝ := dotProduct a (G *ᵥ a)
  have hQuadContinuous : Continuous (fun v : V3 => dotProduct v (G *ᵥ v)) := by
    simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_three]
    fun_prop
  have hPositive (v : V3) (hv : v ≠ 0) : 0 < dotProduct v (G *ᵥ v) := by
    simpa only [star_trivial] using hG.dotProduct_mulVec_pos hv
  obtain ⟨beta,hbeta,hMin⟩ := (isCompact_sphere (0 : V3) 1).exists_forall_le'
    hQuadContinuous.continuousOn (fun v hv => hPositive v (by
      have hn : ‖v‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hv
      intro h
      simp only [h,norm_zero] at hn
      norm_num at hn))
  have hLower (v : V3) : beta*‖v‖^2 ≤ dotProduct v (G *ᵥ v) := by
    by_cases hv : v=0
    · subst v
      simp
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let w : V3 := ‖v‖⁻¹ • v
    have hw : ‖w‖ = 1 := by
      simp only [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
        inv_mul_cancel₀ hn.ne']
    have hMinw := hMin w (by simpa only [Metric.mem_sphere,dist_zero_right] using hw)
    have hBack : ‖v‖ • w = v := by
      simp only [w,smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
    have hScale : dotProduct v (G *ᵥ v) = ‖v‖^2 * dotProduct w (G *ᵥ w) := by
      nth_rw 1 [← hBack]
      nth_rw 2 [← hBack]
      simp only [dotProduct,Matrix.mulVec,Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three]
      ring
    rw [hScale,mul_comm beta (‖v‖^2)]
    exact mul_le_mul_of_nonneg_left hMinw (sq_nonneg ‖v‖)
  have hClosedSphere : IsClosed (metricTangentSphere G ell a) := by
    apply IsClosed.inter
    · apply isClosed_eq
      · change Continuous (fun v : V3 => dotProduct ell v)
        simp only [dotProduct,Fin.sum_univ_three]
        fun_prop
      · exact continuous_const
    · exact isClosed_eq hQuadContinuous continuous_const
  have hBound (v : V3) (hv : v ∈ metricTangentSphere G ell a) : ‖v‖ ≤ A/beta+1 := by
    have hL := hLower v
    rw [hv.2] at hL
    have hSq : ‖v‖^2 ≤ A/beta := by
      apply (le_div_iff₀ hbeta).mpr
      simpa only [mul_comm] using hL
    nlinarith only [hSq,sq_nonneg (‖v‖-(1/2 : ℝ))]
  apply isCompact_iff_isClosed_bounded.mpr
  refine ⟨hClosedSphere,?_⟩
  apply (Metric.isBounded_closedBall (x := (0 : V3)) (r := A/beta+1)).subset
  intro v hv
  apply Metric.mem_closedBall.mpr
  simpa only [dist_zero_right] using hBound v hv

end OAI.AnisotropicCalderon.ProductHessianSeparation

namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
