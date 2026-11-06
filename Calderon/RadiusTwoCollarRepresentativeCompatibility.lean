import Calderon.RadiusTwoEuclideanCollar

/-! Full EXPANSION.json precedes actual collar representative compatibility and zero-extension topology. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma radiusTwoCollarOpens_subset_punctured (q : R3) (b : ℝ) (hPole : ‖(2 : ℝ) • q‖ ≤ b) :
    (radiusTwoCollarOpens b : Set R3) ⊆ (radiusTwoOpens : Set R3) \ {(2 : ℝ) • q} := by
  intro z hz
  refine ⟨SetLike.coe_subset_coe.mpr (radiusTwoCollarOpens_le_radiusTwoOpens b) hz,?_⟩
  intro hp
  have hzq : z = (2 : ℝ) • q := Set.mem_singleton_iff.mp hp
  have hlt : b < ‖(2 : ℝ) • q‖ := by simpa only [hzq] using hz.1
  exact (not_lt_of_ge hPole) hlt

lemma native_zero_cutoff_collar_value_ae_of_row_representative
    (q : R3) (b : ℝ) (hPole : ‖(2 : ℝ) • q‖ ≤ b)
    (chi : R3 → ℝ) (w : RadiusTwoH1Zero) (K : RadiusTwoL2) (G : R3 → ℝ)
    (hValue : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z : R3 => chi z * K z))
    (hRep : G =ᵐ[(volume : Measure R3).restrict
      ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q})] (K : R3 → ℝ))
    (hOne : ∀ z ∈ radiusTwoCollarOpens b, chi z = 1) :
    (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (radiusTwoCollarOpens b)] G := by
  have hN : (volume : Measure R3).restrict (radiusTwoCollarOpens b) ≤
      (volume : Measure R3).restrict radiusTwoOpens :=
    Measure.restrict_mono_set volume
      (SetLike.coe_subset_coe.mpr (radiusTwoCollarOpens_le_radiusTwoOpens b))
  have hP : (volume : Measure R3).restrict (radiusTwoCollarOpens b) ≤
      (volume : Measure R3).restrict ((radiusTwoOpens : Set R3) \ {(2 : ℝ) • q}) :=
    Measure.restrict_mono_set volume (radiusTwoCollarOpens_subset_punctured q b hPole)
  filter_upwards [hValue.filter_mono (ae_mono hN),hRep.filter_mono (ae_mono hP),
    ae_restrict_mem (radiusTwoCollarOpens b).isOpen.measurableSet] with z hv hg hz
  calc
    TauCeti.W1p.value (w : RadiusTwoH1) z = chi z * K z := hv
    _ = K z := by rw [hOne z hz,one_mul]
    _ = G z := hg.symm

lemma zeroExtension_continuousOn_closedBall_sdiff (p : R3) (G : R3 → ℝ)
    (hCont : ContinuousOn G ((radiusTwoOpens : Set R3) \ {p}))
    (hBoundary : ∀ y : R3, ‖y‖ = 2 →
      ContinuousAt (fun z : R3 => if ‖z‖ < 2 then G z else 0) y) :
    ContinuousOn (fun z : R3 => if ‖z‖ < 2 then G z else 0)
      (closedBall (0 : R3) 2 \ {p}) := by
  intro x hx
  have hxNorm : ‖x‖ ≤ 2 := by
    simpa only [mem_closedBall,dist_zero_right] using hx.1
  by_cases hlt : ‖x‖ < 2
  · have hxN : x ∈ (radiusTwoOpens : Set R3) := by
      change x ∈ ball (0 : R3) 2
      exact mem_ball_zero_iff.mpr hlt
    have hxP : x ∈ (radiusTwoOpens : Set R3) \ {p} := ⟨hxN,hx.2⟩
    have hOpen : IsOpen ((radiusTwoOpens : Set R3) \ {p}) :=
      IsOpen.sdiff radiusTwoOpens.isOpen isClosed_singleton
    have hG : ContinuousAt G x := hCont.continuousAt (hOpen.mem_nhds hxP)
    have hEq : (fun z : R3 => if ‖z‖ < 2 then G z else 0) =ᶠ[𝓝 x] G := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hlt)] with z hz
      exact if_pos (mem_ball_zero_iff.mp hz)
    exact (hG.congr_of_eventuallyEq hEq).continuousWithinAt
  · have hx2 : ‖x‖ = 2 := le_antisymm hxNorm (le_of_not_gt hlt)
    exact (hBoundary x hx2).continuousWithinAt

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoCollarOpens_subset_punctured
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.native_zero_cutoff_collar_value_ae_of_row_representative
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.zeroExtension_continuousOn_closedBall_sdiff
