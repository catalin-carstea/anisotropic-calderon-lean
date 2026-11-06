import Calderon.ActualMixedKernelConstruction
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

def fixedSeparationInteriorRoom (B d:ℝ):Set (R3×R3) :=
  {z | ‖z.1‖ < B+1 ∧ ‖z.2‖ < B+1 ∧ d/2 < ‖z.1-z.2‖}

theorem isCompact_fixedSeparationSet (B d:ℝ):IsCompact (fixedSeparationSet B d) := by
  have hClosed:IsClosed {z:R3×R3 | d ≤ ‖z.1-z.2‖} :=
    isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm
  have hEq:fixedSeparationSet B d=(closedBall (0:R3) B×ˢclosedBall (0:R3) B)∩{z:R3×R3 | d ≤ ‖z.1-z.2‖} := by
    ext z
    simp only [fixedSeparationSet,mem_setOf_eq,mem_inter_iff,mem_prod,mem_closedBall,dist_zero_right]
    tauto
  rw [hEq]
  exact ((isCompact_closedBall (0:R3) B).prod (isCompact_closedBall (0:R3) B)).inter_right hClosed

theorem fixedSeparationInteriorRoom_geometry (B d:ℝ) (hd:0 < d):
    IsOpen (fixedSeparationInteriorRoom B d) ∧
      fixedSeparationSet B d⊆fixedSeparationInteriorRoom B d ∧
      fixedSeparationInteriorRoom B d⊆fixedSeparationSet (B+1) (d/2) := by
  refine ⟨(isOpen_lt continuous_fst.norm continuous_const).inter
    ((isOpen_lt continuous_snd.norm continuous_const).inter
      (isOpen_lt continuous_const (continuous_fst.sub continuous_snd).norm)),?_,?_⟩
  · intro z hz
    exact ⟨by linarith only [hz.1],by linarith only [hz.2.1],by linarith only [hz.2.2,hd]⟩
  · intro z hz
    exact ⟨hz.1.le,hz.2.1.le,hz.2.2.le⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
