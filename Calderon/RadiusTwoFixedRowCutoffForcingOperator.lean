import Calderon.RadiusTwoSmoothValueMultiplierExistence
import Calderon.RadiusTwoFixedRowCutoffForcing

/-! Full EXPANSION.json precedes the actual full-Ag forcing operator. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume

theorem exists_radiusTwoFixedRowCutoffForcingOperator
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData) :
    ∃ L : RadiusTwoH1 →L[ℝ] RadiusTwoL2, ∀ u : RadiusTwoH1,
      L u = radiusTwoFixedRowCutoffForcingLp g hg η u := by
  trace "PROOFENTER actual full-Ag forcing operator"
  let μ : Measure R3 := (volume : Measure R3).restrict radiusTwoOpens
  let J (i : Fin 3) : SmoothData :=
    ⟨smoothMetricCutoffFlux g η i,contDiff_smoothMetricCutoffFlux g hg η i⟩
  choose M hM using (fun i : Fin 3 => exists_radiusTwo_smoothValueMultiplier (J i))
  obtain ⟨D,hD⟩ := exists_radiusTwo_smoothValueMultiplier (smoothMetricCutoffFluxDivergence g hg η)
  let G (i : Fin 3) : RadiusTwoH1 →L[ℝ] RadiusTwoL2 :=
    ((innerSL ℝ (coordinateVector i)).compLpL 2 μ).comp TauCeti.W1p.gradientL
  have hG (i : Fin 3) (u : RadiusTwoH1) :
      (G i u : R3 → ℝ) =ᵐ[μ]
        (fun x => ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ) := by
    have h := ContinuousLinearMap.coeFn_compLpL
      (innerSL ℝ (coordinateVector i)) (TauCeti.W1p.gradient u)
    filter_upwards [h] with x hx
    change (G i u) x = ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ
    simp only [innerSL_apply_apply] at hx
    exact hx.trans (real_inner_comm (TauCeti.W1p.gradient u x) (coordinateVector i))
  let A (i : Fin 3) : RadiusTwoH1 →L[ℝ] RadiusTwoL2 := (M i).comp (G i)
  let B : RadiusTwoH1 →L[ℝ] RadiusTwoL2 := D.comp TauCeti.W1p.valueL
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoL2 := ∑ i : Fin 3, A i
  let L : RadiusTwoH1 →L[ℝ] RadiusTwoL2 := (-2 : ℝ) • S - B
  refine ⟨L,?_⟩
  intro u
  trace "ACTUAL COEFFICIENT OPERATORS full-Ag forcing operator"
  have hA (i : Fin 3) : (A i u : R3 → ℝ) =ᵐ[μ]
      (fun x => smoothMetricCutoffFlux g η i x *
        ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ) := by
    filter_upwards [hM i (G i u),hG i u] with x hMx hGx
    change (A i u) x = smoothMetricCutoffFlux g η i x *
      ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ
    change (M i (G i u)) x = smoothMetricCutoffFlux g η i x * (G i u) x at hMx
    exact hMx.trans (congrArg (fun r : ℝ => smoothMetricCutoffFlux g η i x * r) hGx)
  have hS : (S u : R3 → ℝ) =ᵐ[μ] (fun x => ∑ i : Fin 3,
      smoothMetricCutoffFlux g η i x * ⟪TauCeti.W1p.gradient u x,coordinateVector i⟫_ℝ) := by
    have hSum := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin 3)) (fun i => A i u)
    filter_upwards [hSum,ae_all_iff.mpr hA] with x hSumx hAx
    change (S u) x = _
    have hSu : S u = ∑ i : Fin 3, A i u := by simp only [S,ContinuousLinearMap.sum_apply]
    rw [hSu,hSumx]
    exact Finset.sum_congr rfl (fun i _ => hAx i)
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub ((-2 : ℝ) • (S u)) (B u),
    Lp.coeFn_smul (-2 : ℝ) (S u),hS,
    hD (TauCeti.W1p.value u),radiusTwoFixedRowCutoffForcingLp_apply_ae g hg η u]
    with x hSub hSmul hSx hDx hForce
  change (L u) x = (radiusTwoFixedRowCutoffForcingLp g hg η u) x
  change ((-2 : ℝ) • (S u) - B u) x = ((-2 : ℝ) • (S u)) x - (B u) x at hSub
  change ((-2 : ℝ) • (S u)) x = (-2 : ℝ) * (S u) x at hSmul
  change (B u) x = (smoothMetricCutoffFluxDivergence g hg η).1 x * TauCeti.W1p.value u x at hDx
  rw [show L u = (-2 : ℝ) • (S u) - B u by rfl,hSub,hSmul,hSx,hDx,hForce]
  rfl

theorem continuous_radiusTwoFixedRowCutoffForcingLp
    (g : MatrixField) (hg : IsAdmissibleMetric g) (η : SmoothData) :
    Continuous (radiusTwoFixedRowCutoffForcingLp g hg η) := by
  obtain ⟨L,hL⟩ := exists_radiusTwoFixedRowCutoffForcingOperator g hg η
  exact L.continuous.congr (fun u => hL u)

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoFixedRowCutoffForcingOperator
#print axioms OAI.AnisotropicCalderon.ExteriorSource.continuous_radiusTwoFixedRowCutoffForcingLp
