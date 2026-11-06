import MixedKernelObservedOutputRooms
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Filter
open scoped Topology ContDiff

/-- The inverse of the actual tangent phase chart is twice differentiable at its centre.
The chart function and its transverse projection are the originally prescribed ones. -/
theorem tangent_phase_chart_inverse_contDiffAt
    (theta : R3 → ℝ) (htheta : ContDiff ℝ ∞ theta) (p : R3)
    (ell : R3 →L[ℝ] ℝ) (hstrict : HasStrictFDerivAt theta ell p) (hell : ell ≠ 0)
    (hzero : theta p = 0) (e : OpenPartialHomeomorph R3 (ℝ × ell.ker))
    (hps : p ∈ e.source)
    (hformula : ∀ y, e y = (theta y, ell.ker.orthogonalProjectionOnto (y-p))) :
    ContDiffAt ℝ 2 e.symm (0 : ℝ × ell.ker) := by
  let D := PhaseCoordinates.tangentChartData theta ell p hstrict hell
  let L0 := D.leftDeriv.equivProdOfSurjectiveOfIsCompl D.rightDeriv
    D.range_leftDeriv D.range_rightDeriv D.isCompl_ker
  have heq : (e : R3 → ℝ × ell.ker) = D.prodFun := by
    funext y
    exact hformula y
  have hezero : e p = (0 : ℝ × ell.ker) := by
    rw [hformula p, hzero, sub_self, map_zero]
    rfl
  have htarget : (0 : ℝ × ell.ker) ∈ e.target := hezero ▸ e.map_source hps
  have hinverse : e.symm (0 : ℝ × ell.ker) = p := by
    rw [← hezero]
    exact e.left_inv hps
  have hder : HasFDerivAt (e : R3 → ℝ × ell.ker) (L0 : R3 →L[ℝ] ℝ × ell.ker) p := by
    rw [heq]
    exact D.hasStrictFDerivAt.hasFDerivAt
  have hsmooth : ContDiff ℝ 2 (e : R3 → ℝ × ell.ker) := by
    rw [show (e : R3 → ℝ × ell.ker) =
      (fun y => (theta y, ell.ker.orthogonalProjectionOnto (y-p))) from funext hformula]
    exact (htheta.of_le (by simp)).prodMk
      (ell.ker.orthogonalProjectionOnto.contDiff.comp (contDiff_id.sub contDiff_const))
  apply e.contDiffAt_symm htarget
  · rw [hinverse]
    exact hder
  · rw [hinverse]
    exact hsmooth.contDiffAt

/-- The prescribed second covector becomes the literal first projection in its own chart. -/
theorem prescribed_second_slice_fderiv_phase_coordinates
    (rho : R3 × R3 → ℝ) (theta : R3 → ℝ) (p1 p2 : R3)
    (ell : R3 →L[ℝ] ℝ)
    (hrho : DifferentiableAt ℝ rho (p1,p2))
    (htheta : HasFDerivAt theta ell p2)
    (hpartial : (fderiv ℝ rho (p1,p2)).comp (ContinuousLinearMap.inr ℝ R3 R3) = ell)
    (e : OpenPartialHomeomorph R3 (ℝ × ell.ker))
    (htarget : (0 : ℝ × ell.ker) ∈ e.target)
    (hinverse : e.symm (0 : ℝ × ell.ker) = p2)
    (hformula : ∀ y, e y = (theta y, ell.ker.orthogonalProjectionOnto (y-p2)))
    (hInv : DifferentiableAt ℝ e.symm (0 : ℝ × ell.ker)) :
    fderiv ℝ (fun q : ℝ × ell.ker => rho (p1,e.symm q)) 0 =
      ContinuousLinearMap.fst ℝ ℝ ell.ker := by
  have hslice : HasFDerivAt (fun y => rho (p1,y)) ell p2 := by
    have hd := hrho.hasFDerivAt.comp p2 (hasFDerivAt_prodMk_right p1 p2)
    change HasFDerivAt (fun y : R3 => rho (p1,y))
      ((fderiv ℝ rho (p1,p2)).comp (ContinuousLinearMap.inr ℝ R3 R3)) p2 at hd
    rw [hpartial] at hd
    exact hd
  have hslicep : HasFDerivAt (fun y => rho (p1,y)) ell (e.symm (0 : ℝ × ell.ker)) := by
    rw [hinverse]
    exact hslice
  have hthetap : HasFDerivAt theta ell (e.symm (0 : ℝ × ell.ker)) := by
    rw [hinverse]
    exact htheta
  have hrhoc := hslicep.comp (0 : ℝ × ell.ker) hInv.hasFDerivAt
  have hthetac := hthetap.comp (0 : ℝ × ell.ker) hInv.hasFDerivAt
  have hevent : (fun q : ℝ × ell.ker => theta (e.symm q)) =ᶠ[𝓝 0] Prod.fst := by
    filter_upwards [e.open_target.mem_nhds htarget] with q hq
    have h := congrArg Prod.fst (e.right_inv hq)
    simpa only [hformula] using h
  have hproj : HasFDerivAt (fun q : ℝ × ell.ker => theta (e.symm q))
      (ContinuousLinearMap.fst ℝ ℝ ell.ker) 0 :=
    (hasFDerivAt_fst : HasFDerivAt Prod.fst
      (ContinuousLinearMap.fst ℝ ℝ ell.ker) (0 : ℝ × ell.ker)).congr_of_eventuallyEq hevent
  exact hrhoc.fderiv.trans (hthetac.unique hproj)

/-- A genuine open neighbourhood where increasing the second phase height increases rho.
This follows from the prescribed covector, rather than being an extra final assumption. -/
theorem exists_positive_second_chart_height_neighborhood
    (rho : R3 × R3 → ℝ) (theta : R3 → ℝ) (p1 p2 : R3)
    (ell : R3 →L[ℝ] ℝ)
    (hrho : ContDiffAt ℝ 2 rho (p1,p2))
    (htheta : HasFDerivAt theta ell p2)
    (hpartial : (fderiv ℝ rho (p1,p2)).comp (ContinuousLinearMap.inr ℝ R3 R3) = ell)
    (e : OpenPartialHomeomorph R3 (ℝ × ell.ker))
    (htarget : (0 : ℝ × ell.ker) ∈ e.target)
    (hinverse : e.symm (0 : ℝ × ell.ker) = p2)
    (hformula : ∀ y, e y = (theta y, ell.ker.orthogonalProjectionOnto (y-p2)))
    (hInv : ContDiffAt ℝ 2 e.symm (0 : ℝ × ell.ker)) :
    ∃ V : Set (R3 × (ℝ × ell.ker)), IsOpen V ∧ (p1,0) ∈ V ∧
      ∀ z ∈ V,
        ContDiffAt ℝ 2 (fun w : R3 × (ℝ × ell.ker) => rho (w.1,e.symm w.2)) z ∧
        0 < (fderiv ℝ (fun w : R3 × (ℝ × ell.ker) => rho (w.1,e.symm w.2)) z)
          (0,(1,0)) := by
  let Q : R3 × (ℝ × ell.ker) → ℝ := fun w => rho (w.1,e.symm w.2)
  have hmap : ContDiffAt ℝ 2
      (fun w : R3 × (ℝ × ell.ker) => (w.1,e.symm w.2)) (p1,0) :=
    contDiffAt_fst.prodMk (hInv.comp (p1,0) contDiffAt_snd)
  have hrhop : ContDiffAt ℝ 2 rho (p1,e.symm (0 : ℝ × ell.ker)) := by
    rw [hinverse]
    exact hrho
  have hQ : ContDiffAt ℝ 2 Q (p1,0) := hrhop.comp (p1,0) hmap
  have hQdiff : DifferentiableAt ℝ Q (p1,0) := hQ.differentiableAt (by norm_num)
  have hslice := hQdiff.hasFDerivAt.comp (0 : ℝ × ell.ker)
    (hasFDerivAt_prodMk_right p1 (0 : ℝ × ell.ker))
  have hsliceExact := prescribed_second_slice_fderiv_phase_coordinates rho theta p1 p2 ell
    (hrho.differentiableAt (by norm_num)) htheta hpartial e htarget hinverse hformula
    (hInv.differentiableAt (by norm_num))
  have hcomp : (fderiv ℝ Q (p1,0)).comp (ContinuousLinearMap.inr ℝ R3 (ℝ × ell.ker)) =
      ContinuousLinearMap.fst ℝ ℝ ell.ker := by
    exact hslice.fderiv.symm.trans hsliceExact
  have hheight : (fderiv ℝ Q (p1,0)) (0,(1,0)) = 1 := by
    have heval := congrArg (fun A : (ℝ × ell.ker) →L[ℝ] ℝ => A (1,0)) hcomp
    change (fderiv ℝ Q (p1,0)) (0,(1,0)) = 1 at heval
    exact heval
  have hc : ContinuousAt (fun z => (fderiv ℝ Q z) (0,(1,0))) (p1,0) :=
    (hQ.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hpos : {z | 0 < (fderiv ℝ Q z) (0,(1,0))} ∈ 𝓝 (p1,0) := by
    exact hc.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by rw [hheight]; norm_num))
  obtain ⟨V,hVsub,hVo,hVm⟩ := mem_nhds_iff.mp ((hQ.eventually (by norm_num)).and hpos)
  exact ⟨V,hVo,hVm,fun z hz => hVsub hz⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
