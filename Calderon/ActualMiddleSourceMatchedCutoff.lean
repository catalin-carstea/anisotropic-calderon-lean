import Calderon.ActualMiddleCompactBufferGeometry
import Calderon.ActualReferenceRadiusInterpolationScale
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.FDeriv.Const

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology Manifold
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open ConformalDepth RadiusProfile

/-- The exact middle set has one fixed cutoff supported strictly inside the
original cylinder. Its derivative support lies in the two source regions, and
the same cutoff equals one on all sufficiently small closed interpolation
balls, with the radius threshold chosen before `δ`. -/
theorem exists_actual_middle_source_matched_cutoff
    (L R : ℝ) (p : ℕ) (hL : 0 < L) (hR : 0 < R) :
    ∃ tb : ℝ, 0 < tb ∧ 3 * tb < depthPrimitive L (1/8) (1/4) ∧
      let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
        referenceDepth L y ≤ 2 * tb}
      IsCompact K ∧ K ⊆ interior cylinder ∧
      ∃ chi : R3 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
        range chi ⊆ Icc 0 1 ∧
        tsupport chi ⊆ interior cylinder ∧
        ∃ W : Set R3, IsOpen W ∧ K ⊆ W ∧
          (∀ z ∈ W, chi z = 1) ∧
          tsupport (fderiv ℝ chi) ⊆
            {z : R3 | z 2 < -(1/4 : ℝ)} ∪
              {z : R3 | tb < referenceDepth L z} ∧
          ∃ rho : ℝ, 0 < rho ∧
            ∀ δ : ℝ, 0 < δ → ∀ y ∈ K,
              referenceRadius δ R p L y < rho →
                let s := (referenceRadius δ R p L y) ^ ((1 : ℝ) / 23)
                closedBall y s ⊆ W ∧
                closedBall y s ⊆ interior cylinder ∧
                closedBall y s ⊆ closedBall (0 : R3) 3 ∧
                ∀ z ∈ closedBall y s, chi z = 1 := by
  obtain ⟨tb,htb,hthree,hKcompact,hKinterior⟩ :=
    exists_actual_middle_compact_interior_buffer L hL
  let K : Set R3 := {y | y ∈ cylinder ∧ -(1/2 : ℝ) ≤ y 2 ∧
    referenceDepth L y ≤ 2 * tb}
  have hKball : K ⊆ ball (0 : R3) 3 := by
    intro y hy
    have hyC : y ∈ cylinder := interior_subset (hKinterior hy)
    have hn := norm_le_two_of_mem_cylinder y hyC
    apply mem_ball_zero_iff.mpr
    linarith
  let V : Set R3 := interior cylinder ∩ ball (0 : R3) 3
  have hVopen : IsOpen V := isOpen_interior.inter isOpen_ball
  have hKV : K ⊆ V := fun y hy => ⟨hKinterior hy,hKball hy⟩
  obtain ⟨sigma,hsigma,hRoom⟩ :=
    hKcompact.exists_cthickening_subset_open hVopen hKV
  let tau : ℝ := sigma / 2
  have htau : 0 < tau := by dsimp [tau]; positivity
  have htausigma : tau < sigma := by dsimp [tau]; linarith
  let W : Set R3 := thickening tau K
  let U : Set R3 := thickening sigma K
  let T : Set R3 := cthickening tau K
  have hWopen : IsOpen W := isOpen_thickening
  have hKW : K ⊆ W := self_subset_thickening htau K
  have hTclosed : IsClosed T := isClosed_cthickening
  have hTU : T ⊆ U := cthickening_subset_thickening' hsigma htausigma K
  obtain ⟨chi,hCMDiff,hRange,hSupport,hOne⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (I := 𝓘(ℝ, R3)) (n := ⊤)
      isOpen_thickening hTclosed hTU
  have hDiff : ContDiff ℝ ∞ chi := by
    simpa [contMDiff_iff_contDiff] using hCMDiff
  have hTsupport : tsupport chi ⊆ V := by
    change closure (Function.support chi) ⊆ V
    rw [hSupport]
    exact (closure_thickening_subset_cthickening sigma K).trans hRoom
  have hCompact : HasCompactSupport chi := by
    apply hasCompactSupport_def.mpr
    apply (isCompact_closedBall (0 : R3) 3).of_isClosed_subset (isClosed_tsupport chi)
    exact hTsupport.trans (inter_subset_right.trans ball_subset_closedBall)
  have hWOne : ∀ z ∈ W, chi z = 1 := by
    intro z hz
    exact (hOne z).mp (thickening_subset_cthickening tau K hz)
  have hSupportDerivAvoid : Function.support (fderiv ℝ chi) ⊆ Wᶜ := by
    intro z hz hzW
    have hEvent : chi =ᶠ[𝓝 z] (fun _ : R3 => (1 : ℝ)) := by
      filter_upwards [hWopen.mem_nhds hzW] with x hx
      exact hWOne x hx
    have hZero : fderiv ℝ chi z = 0 := by
      rw [hEvent.fderiv_eq]
      simp
    exact hz hZero
  have hTsupportDerivAvoid : tsupport (fderiv ℝ chi) ⊆ Wᶜ :=
    closure_minimal hSupportDerivAvoid hWopen.isClosed_compl
  have hDerivRegion : tsupport (fderiv ℝ chi) ⊆
      {z : R3 | z 2 < -(1/4 : ℝ)} ∪
        {z : R3 | tb < referenceDepth L z} := by
    intro z hz
    have hzI : z ∈ interior cylinder :=
      hTsupport.trans (inter_subset_left) ((tsupport_fderiv_subset ℝ) hz)
    by_contra hn
    have hzNotLower : ¬ z 2 < -(1/4 : ℝ) := by
      intro h
      exact hn (Or.inl h)
    have hzNotUpper : ¬ tb < referenceDepth L z := by
      intro h
      exact hn (Or.inr h)
    have hzK : z ∈ K := by
      refine ⟨interior_subset hzI,?_,?_⟩
      · linarith
      · linarith
    exact hTsupportDerivAvoid hz (hKW hzK)
  let rho : ℝ := tau^23
  have hrho : 0 < rho := pow_pos htau _
  refine ⟨tb,htb,hthree,hKcompact,hKinterior,chi,hDiff,hCompact,hRange,
    hTsupport.trans inter_subset_left,W,hWopen,hKW,hWOne,hDerivRegion,
    rho,hrho,?_⟩
  intro δ hδ y hy hrsmall
  dsimp
  let r : ℝ := referenceRadius δ R p L y
  let s : ℝ := r ^ ((1 : ℝ) / 23)
  have hr : 0 < r := referenceRadius_pos δ R p L y hδ hR
  have hsPow : s^23 = r := by
    dsimp [s]
    convert Real.rpow_inv_natCast_pow hr.le (by norm_num : (23 : ℕ) ≠ 0) using 1 <;> norm_num
  have hsTau : s < tau := by
    apply lt_of_pow_lt_pow_left₀ 23 htau.le
    rw [hsPow]
    exact hrsmall
  have hClosedW : closedBall y s ⊆ W :=
    (closedBall_subset_cthickening hy s).trans
      (cthickening_subset_thickening' htau hsTau K)
  have hWRoom : W ⊆ V :=
    (thickening_subset_cthickening tau K).trans
      ((cthickening_mono htausigma.le K).trans hRoom)
  refine ⟨hClosedW,?_,?_,?_⟩
  · exact (hClosedW.trans hWRoom).trans inter_subset_left
  · exact (hClosedW.trans hWRoom).trans
      (inter_subset_right.trans ball_subset_closedBall)
  · intro z hz
    exact hWOne z (hClosedW hz)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
