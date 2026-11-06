import Calderon.ActualUniformNativeSpectrumPowerBound
import MixedKernelCurrentCrossSeries
import Mathlib.Topology.MetricSpace.Thickening
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Regularity.classicalHarmonicL2Space harmonicRestrict

theorem exists_uniform_fixed_room_harmonicRestrict_spectrum_power_bound
    (S:KnownSideSourceData) (D K T KT:Set R3) (hD:IsOpen D) (hK:IsCompact K) (hDK:D⊆K)
    (hT:IsOpen T) (hTne:T.Nonempty) (hKT:IsCompact KT) (hTKT:T⊆KT) (hKTD:KT⊆D)
    (beta:ℝ) (hbeta:0 < beta) :
    ∃ lambda0 P:ℝ,0 < lambda0 ∧ lambda0 ≤ 1 ∧ 1 ≤ P ∧
      ∀ lambda∈Icc (0:ℝ) lambda0,∀ hTD:T⊆D,∀ (iota:Type)
      (w:iota→harmonicSub D hD (dilatedFirstPrincipal S lambda)
        (contDiff_dilatedFirstPrincipal S lambda).contDiffOn),Orthonormal ℝ w →
      ∀ mu:iota→ℝ,(∀ j,0 < mu j) → (∀ j,mu j ≤ 1) →
      (∀ j l,inner ℝ (harmonicRestrict D hD (dilatedFirstPrincipal S lambda)
          (contDiff_dilatedFirstPrincipal S lambda).contDiffOn T hTD (w j))
        (harmonicRestrict D hD (dilatedFirstPrincipal S lambda)
          (contDiff_dilatedFirstPrincipal S lambda).contDiffOn T hTD (w l))=
        if j=l then mu j^2 else 0) → (∑' j,mu j^beta) ≤ P := by
  obtain ⟨B0,hB0⟩ := hK.exists_bound_of_continuousOn (continuous_id:Continuous (fun x:R3 => x)).continuousOn
  let B:ℝ := max B0 1+1
  have hB:0 < B := by dsimp only [B];positivity
  have hDB:D⊆ball (0:R3) B := by
    intro x hx
    rw [mem_ball,dist_zero_right]
    have hh := hB0 x (hDK hx)
    exact hh.trans_lt (by dsimp only [B];linarith only [le_max_left B0 1])
  have hCl:closure T⊆KT := closure_minimal hTKT hKT.isClosed
  have hTC:IsCompact (closure T) := hKT.of_isClosed_subset isClosed_closure hCl
  obtain ⟨eps,heps,hThick⟩ := hTC.exists_cthickening_subset_open hD (hCl.trans hKTD)
  let d:ℝ := eps/2
  have hd:0 < d := half_pos heps
  have hBuffer:∀ x∈closure T,closedBall x (2*d)⊆D := by
    intro x hx z hz
    apply hThick
    apply Metric.mem_cthickening_of_dist_le z x eps (closure T) hx
    have hh := mem_closedBall.mp hz
    dsimp only [d] at hh
    linarith only [hh]
  let gs:Fin 2→MatrixField := ![S.g1,S.g2]
  have hgs:∀ i:Fin 2,IsAdmissibleMetric (gs i) := by
    intro i
    fin_cases i
    · exact S.g1_admissible
    · exact S.g2_admissible
  obtain ⟨lambda0,hlambda0,hlambda01,hRoom,H⟩ :=
    exists_uniform_native_harmonicRestrict_spectrum_power_bound gs hgs B hB 1 (by norm_num)
  obtain ⟨P,hP,HP⟩ := H 0 beta hbeta d hd
  refine ⟨lambda0,P,hlambda0,hlambda01,hP,?_⟩
  intro lambda hlam hTD iota w hw mu hmu hmu1 hgram
  exact HP lambda hlam D hD hDB T hT hTne hTC hBuffer hTD iota w hw mu hmu hmu1 hgram

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
