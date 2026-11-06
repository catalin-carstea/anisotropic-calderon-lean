import Calderon.ActualTwoMetricSeparatelySmoothSourceKernels
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily
attribute [local instance] Classical.propDecidable

theorem aestronglyMeasurable_radiusTwo_poleSection_fderiv_apply
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (S : Set R3) (hS : MeasurableSet S) (hSB : S ⊆ (radiusTwoOpens : Set R3))
    (U : Set R3) (hU : IsOpen U) (hUB : U ⊆ (radiusTwoOpens : Set R3))
    (p : R3) (hp : p ∈ U) (hpS : p ∉ S) (v : R3) :
    AEStronglyMeasurable
      (fun z : R3 => if hz : z ∈ (radiusTwoOpens : Set R3) then
        fderiv ℝ (radiusTwoKernelPoleSection G ⟨z,hz⟩) p v else 0)
      (((volume : Measure R3).restrict radiusTwoOpens).restrict S) := by
  let μB : Measure R3 := (volume : Measure R3).restrict radiusTwoOpens
  let ν : Measure R3 := μB.restrict S
  have hpB : p ∈ (radiusTwoOpens : Set R3) := hUB hp
  let pB : (radiusTwoOpens : Set R3) := ⟨p,hpB⟩
  obtain ⟨ε, hε, hBall⟩ : ∃ ε : ℝ, 0 < ε ∧ ball p ε ⊆ U :=
    Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let δ : ℝ := ε / (2 * (1 + ‖v‖))
  have hDen : 0 < 2 * (1 + ‖v‖) := by positivity
  have hδ : 0 < δ := div_pos hε hDen
  have hδEq : δ * (2 * (1 + ‖v‖)) = ε := div_mul_cancel₀ ε (ne_of_gt hDen)
  have hδNorm : δ * ‖v‖ < ε := by nlinarith [mul_nonneg hδ.le (norm_nonneg v)]
  let t : ℕ → ℝ := fun n => δ / ((n : ℝ) + 1)
  have htPos (n : ℕ) : 0 < t n := div_pos hδ (by positivity)
  have htLe (n : ℕ) : t n ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg (α := ℝ) n)]
  have hqU (n : ℕ) : p + t n • v ∈ U := by
    apply hBall
    apply mem_ball_iff_norm.mpr
    have hSub : p + t n • v - p = t n • v := by abel
    rw [hSub, norm_smul, Real.norm_eq_abs, abs_of_pos (htPos n)]
    exact (mul_le_mul_of_nonneg_right (htLe n) (norm_nonneg v)).trans_lt hδNorm
  have hqB (n : ℕ) : p + t n • v ∈ (radiusTwoOpens : Set R3) := hUB (hqU n)
  let qB (n : ℕ) : (radiusTwoOpens : Set R3) := ⟨p + t n • v, hqB n⟩
  have htZero : Tendsto t atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_const_nhds (x := δ)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [t, div_eq_mul_inv, one_div, one_mul, mul_zero] using h
  have htRight : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htZero, Eventually.of_forall htPos⟩
  have hRowMeasurable (q : (radiusTwoOpens : Set R3)) :
      AEStronglyMeasurable (G q) ν := by
    have hRow : AEStronglyMeasurable (G q) μB :=
      (Lp.aestronglyMeasurable (K q)).congr ((hData.1 q).2.2.1.symm)
    exact hRow.mono_measure Measure.restrict_le_self
  let s : ℕ → R3 → ℝ := fun n z => (t n)⁻¹ • (G (qB n) z - G pB z)
  have hs (n : ℕ) : AEStronglyMeasurable (s n) ν :=
    ((hRowMeasurable (qB n)).sub (hRowMeasurable pB)).const_smul ((t n)⁻¹)
  have hSeparate := IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth
    hreg hcalc g hg K G hData
  have hLimit : ∀ᵐ z ∂ν, Tendsto (fun n => s n z) atTop
      (𝓝 (if hz : z ∈ (radiusTwoOpens : Set R3) then
        fderiv ℝ (radiusTwoKernelPoleSection G ⟨z,hz⟩) p v else 0)) := by
    filter_upwards [ae_restrict_mem hS] with z hzS
    have hzB : z ∈ (radiusTwoOpens : Set R3) := hSB hzS
    let zB : (radiusTwoOpens : Set R3) := ⟨z,hzB⟩
    have hpOff : p ∈ (radiusTwoOpens : Set R3) \ {z} := by
      refine ⟨hpB, ?_⟩
      intro hpz
      exact hpS ((mem_singleton_iff.mp hpz).symm ▸ hzS)
    have hOffOpen : IsOpen ((radiusTwoOpens : Set R3) \ {z}) :=
      IsOpen.sdiff radiusTwoOpens.isOpen isClosed_singleton
    have hAt : ContDiffAt ℝ ∞ (radiusTwoKernelPoleSection G zB) p :=
      (hSeparate.2.2 zB).contDiffAt (hOffOpen.mem_nhds hpOff)
    let Φ : ℝ → ℝ := fun a => radiusTwoKernelPoleSection G zB (p + a • v)
    have hLine := (hAt.differentiableAt (by simp)).hasFDerivAt.hasLineDerivAt v
    have hScalarLine : HasDerivAt Φ
        (fderiv ℝ (radiusTwoKernelPoleSection G zB) p v) 0 := by
      change HasDerivAt _ _ (0 : ℝ) at hLine
      apply hLine.congr_of_eventuallyEq
      exact Eventually.of_forall (fun a =>
        congrArg (radiusTwoKernelPoleSection G zB)
          (WithLp.ofLp_injective (2 : ENNReal) (funext (fun j => by rfl))))
    have hSlope : Tendsto
        (fun n => (t n)⁻¹ • (Φ (t n) - Φ 0)) atTop
        (𝓝 (fderiv ℝ (radiusTwoKernelPoleSection G zB) p v)) := by
      simpa only [Function.comp_def, zero_add] using
        hScalarLine.tendsto_slope_zero_right.comp htRight
    have hValue (n : ℕ) : Φ (t n) = G (qB n) z := by
      calc
        Φ (t n) = radiusTwoKernelPoleSection G zB (qB n) := by
          apply congrArg (radiusTwoKernelPoleSection G zB)
          exact WithLp.ofLp_injective (2 : ENNReal) (funext (fun j => by rfl))
        _ = _ := by
          simp only [radiusTwoKernelPoleSection, dif_pos (hqB n), qB, zB]
    have hValue0 : Φ 0 = G pB z := by
      calc
        Φ 0 = radiusTwoKernelPoleSection G zB pB := by
          apply congrArg (radiusTwoKernelPoleSection G zB)
          apply WithLp.ofLp_injective (2 : ENNReal)
          funext j
          change p j + (0 : ℝ) * v j = p j
          simp only [zero_mul, add_zero]
        _ = _ := by
          simp only [radiusTwoKernelPoleSection, dif_pos hpB, pB, zB]
    have hSeq : Tendsto (fun n => s n z) atTop
        (𝓝 (fderiv ℝ (radiusTwoKernelPoleSection G zB) p v)) :=
      Tendsto.congr' (Eventually.of_forall (fun n =>
        congrArg₂ (fun a b : ℝ => (t n)⁻¹ • (a-b)) (hValue n) hValue0)) hSlope
    simpa only [dif_pos hzB] using hSeq
  exact aestronglyMeasurable_of_tendsto_ae atTop hs hLimit

end OAI.AnisotropicCalderon.ExteriorSource

#print axioms OAI.AnisotropicCalderon.ExteriorSource.aestronglyMeasurable_radiusTwo_poleSection_fderiv_apply
