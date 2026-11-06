import Calderon.NativeSmoothBallH1Approximation
import TauCeti.Analysis.Sobolev.W1p.MeyersSerrin

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem exists_compactSupport_smoothData_native_H1_approximation
    (u : BallH1) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : SmoothData, HasCompactSupport w.1 ∧ ‖smoothSobolev w-u‖ < ε := by
  obtain ⟨v,f,hf,hValue,hv⟩ :=
    TauCeti.W1p.exists_contDiffOn_approximation (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num) u
  have hvNorm : Tendsto (fun n : ℕ => ‖v n-u‖) atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hv
  have hvSmall : ∀ᶠ n : ℕ in atTop, ‖v n-u‖ < ε/2 :=
    hvNorm.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨n,hn⟩ := hvSmall.exists
  obtain ⟨w,hwc,hw⟩ := exists_smoothData_close_of_smooth_ball_representative
    (v n) (f n) (hf n) (hValue n) (ε/2) (half_pos hε)
  refine ⟨w,hwc,?_⟩
  calc
    ‖smoothSobolev w-u‖ ≤ ‖smoothSobolev w-v n‖ + ‖v n-u‖ :=
      calc
        _ = ‖(smoothSobolev w-v n)+(v n-u)‖ :=
          congrArg norm (sub_add_sub_cancel (smoothSobolev w) (v n) u).symm
        _ ≤ _ := norm_add_le _ _
    _ < ε/2 + ε/2 := add_lt_add hw hn
    _ = ε := add_halves ε

theorem denseRange_smoothSobolev : DenseRange smoothSobolev := by
  apply Metric.denseRange_iff.mpr
  intro u ε hε
  obtain ⟨w,_,hw⟩ := exists_compactSupport_smoothData_native_H1_approximation u ε hε
  refine ⟨w,?_⟩
  rw [dist_comm,dist_eq_norm]
  exact hw

end OAI.AnisotropicCalderon.DirichletFamily
