import Calderon.SmoothMetricCutoffFlux
import Mathlib.MeasureTheory.Function.L2Space

/-! EXPANSION.json precedes actual L2 forcing derived from a FIXED native H1 row. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume

theorem memLp_radiusTwo_continuous_mul
    (a : R3 → ℝ) (ha : Continuous a) {f : R3 → ℝ}
    (hf : MemLp f 2 ((volume : Measure R3).restrict radiusTwoOpens)) :
    MemLp (fun x : R3 => a x * f x) 2 ((volume : Measure R3).restrict radiusTwoOpens) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : R3) 2).bddAbove_image ha.norm.continuousOn
  apply hf.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem radiusTwoOpens.isOpen.measurableSet] with x hx
  have hxB : x ∈ closedBall (0 : R3) 2 := ball_subset_closedBall hx
  have hAx : ‖a x‖ ≤ C := hC ⟨x,hxB,rfl⟩
  simp only [Pi.mul_apply,norm_mul]
  exact mul_le_mul_of_nonneg_right hAx (norm_nonneg _)

def radiusTwoFixedRowCutoffForcing (g : MatrixField) (hg : IsAdmissibleMetric g)
    (η : SmoothData) (u : RadiusTwoH1) (x : R3) : ℝ :=
  (-2 : ℝ) * (∑ i : Fin 3, smoothMetricCutoffFlux g η i x *
    ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ) -
    (smoothMetricCutoffFluxDivergence g hg η).1 x * TauCeti.W1p.value u x

theorem memLp_radiusTwoFixedRowCutoffForcing
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData) (u : RadiusTwoH1) :
    MemLp (radiusTwoFixedRowCutoffForcing g hg η u) 2
      ((volume : Measure R3).restrict radiusTwoOpens) := by
  have hTerm (i : Fin 3) : MemLp (fun x : R3 => smoothMetricCutoffFlux g η i x *
      ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ) 2
        ((volume : Measure R3).restrict radiusTwoOpens) :=
    memLp_radiusTwo_continuous_mul (smoothMetricCutoffFlux g η i)
      (contDiff_smoothMetricCutoffFlux g hg η i).continuous
      ((Lp.memLp (TauCeti.W1p.gradient u)).inner_const (coordinateVector i))
  have hSum : MemLp (fun x : R3 => ∑ i : Fin 3, smoothMetricCutoffFlux g η i x *
      ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ) 2
        ((volume : Measure R3).restrict radiusTwoOpens) := by
    simpa only using memLp_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => hTerm i)
  have hDiv : MemLp (fun x : R3 => (smoothMetricCutoffFluxDivergence g hg η).1 x *
      TauCeti.W1p.value u x) 2 ((volume : Measure R3).restrict radiusTwoOpens) :=
    memLp_radiusTwo_continuous_mul (smoothMetricCutoffFluxDivergence g hg η).1
      (smoothMetricCutoffFluxDivergence g hg η).2.continuous (Lp.memLp (TauCeti.W1p.value u))
  refine MemLp.ae_eq ?_ ((hSum.const_mul (-2 : ℝ)).sub hDiv)
  apply Filter.Eventually.of_forall
  intro x
  change (-2 : ℝ) * (∑ i : Fin 3, smoothMetricCutoffFlux g η i x *
    ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ) -
    (smoothMetricCutoffFluxDivergence g hg η).1 x * TauCeti.W1p.value u x =
      radiusTwoFixedRowCutoffForcing g hg η u x
  rfl

def radiusTwoFixedRowCutoffForcingLp (g : MatrixField) (hg : IsAdmissibleMetric g)
    (η : SmoothData) (u : RadiusTwoH1) : RadiusTwoL2 :=
  (memLp_radiusTwoFixedRowCutoffForcing g hg η u).toLp (radiusTwoFixedRowCutoffForcing g hg η u)

theorem radiusTwoFixedRowCutoffForcingLp_apply_ae
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData) (u : RadiusTwoH1) :
    (radiusTwoFixedRowCutoffForcingLp g hg η u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] radiusTwoFixedRowCutoffForcing g hg η u :=
  MemLp.coeFn_toLp (memLp_radiusTwoFixedRowCutoffForcing g hg η u)

end OAI.AnisotropicCalderon.ExteriorSource
