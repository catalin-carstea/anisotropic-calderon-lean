import Calderon.RadiusTwoCommonRowBoundaryCollarData
import Calderon.RadiusTwoNativeFixedCollarBoundaryZero

/-! Full EXPANSION.json precedes actual SAME-K source-specific boundary realization. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Distributions Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open EnergyBridge DirichletFamily TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

theorem exists_radiusTwoCommonRow_boundary_continuous_representative
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K)) :
    ∃ F : R3 → ℝ,
      ContinuousOn F (closedBall (0 : R3) 2 \ {(2 : ℝ) • q}) ∧
      F =ᵐ[(volume : Measure R3).restrict ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})]
        (K : R3 → ℝ) ∧
      (∀ y : R3, ‖y‖ = 2 → F y = 0 ∧ ContinuousAt F y) := by
  refine Exists.elim (exists_radiusTwoCommonRow_native_boundary_collar_data
    hreg hcalc g hg a ha ha1 q hq K hLimit) ?_
  intro b hB
  refine Exists.elim hB ?_
  intro w hW
  refine Exists.elim hW ?_
  intro G hG
  rcases hG with ⟨hb1,hb2,hCont,hRep,hContCollar,hValue,hWeak⟩
  obtain ⟨b2,M,hbb2,hb22,hM,hPoint,hBoundary⟩ :=
    exists_native_fixed_collar_barrier_and_boundary_zero w G b hb1 hb2 hWeak hContCollar hValue
  let F : R3 → ℝ := fun z : R3 => if ‖z‖ < 2 then G z else 0
  have hContF : ContinuousOn F (closedBall (0 : R3) 2 \ {(2 : ℝ) • q}) :=
    zeroExtension_continuousOn_closedBall_sdiff ((2 : ℝ) • q) G hCont
      (fun y hy => (hBoundary y hy).2)
  have hOpen : IsOpen ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) :=
    IsOpen.sdiff radiusTwoOpens.isOpen isClosed_singleton
  have hRepF : F =ᵐ[(volume : Measure R3).restrict
      ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})] (K : R3 → ℝ) := by
    filter_upwards [hRep,ae_restrict_mem hOpen.measurableSet] with z hz hzN
    have hNorm : ‖z‖ < 2 := by
      have hzBall : z ∈ ball (0 : R3) 2 := hzN.1
      exact mem_ball_zero_iff.mp hzBall
    change (if ‖z‖ < 2 then G z else 0) = K z
    rw [if_pos hNorm]
    exact hz
  exact ⟨F,hContF,hRepF,hBoundary⟩

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.exists_radiusTwoCommonRow_boundary_continuous_representative
