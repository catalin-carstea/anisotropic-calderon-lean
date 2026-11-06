import Calderon.RadiusTwoCommonRowCollarCompactEquation
import Calderon.NativeFixedFunctionTestEquationExtension
import Calderon.NativeCollarHarmonicRestriction

/-! EXPANSION.json precedes the derived SAME-K actual collar equation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric Filter TopologicalSpace
open scoped ENNReal Distributions ContDiff Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open EnergyBridge TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

theorem radiusTwoCommonRow_cutoff_collar_weak_equation
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (chi : R3 → ℝ) (w : RadiusTwoH1Zero)
    (hValue : (W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z : R3 => chi z * K z))
    (b : ℝ) (hb : 1 ≤ b) (hPole : ‖(2 : ℝ) • q‖ ≤ b)
    (hOne : ∀ z ∈ radiusTwoCollarOpens b, chi z = 1)
    (v : W1p0 (volume : Measure R3) (radiusTwoCollarOpens b) 2) :
    energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens b) (w : RadiusTwoH1))
      (v : W1p (volume : Measure R3) (radiusTwoCollarOpens b) 2) = 0 := by
  have hCompact : ∀ phi : 𝓓(radiusTwoCollarOpens b, ℝ),
      energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens b) (w : RadiusTwoH1))
        (W1p.ofTestFunctionₗ (volume : Measure R3) (radiusTwoCollarOpens b) 2 phi) =
        ∫ z in radiusTwoCollarOpens b,
          (0 : Lp ℝ 2 ((volume : Measure R3).restrict (radiusTwoCollarOpens b))) z * phi z
            ∂(volume : Measure R3) := by
    intro phi
    have hEq : energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (0 : R3 → R3) (0 : R3 → ℝ)
        (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens b) (w : RadiusTwoH1))
        (W1p.ofTestFunctionₗ (volume : Measure R3) (radiusTwoCollarOpens b) 2 phi) = 0 := by
      simpa only [nativeZeroTestLinear_coe] using
        radiusTwoCommonRow_cutoff_collar_compact_equation
          g hg a ha ha1 q hq K hLimit chi w hValue b hb hPole hOne phi
    have hIntegral : (∫ z in radiusTwoCollarOpens b,
        (0 : Lp ℝ 2 ((volume : Measure R3).restrict (radiusTwoCollarOpens b))) z * phi z
          ∂(volume : Measure R3)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞))
        (μ := (volume : Measure R3).restrict (radiusTwoCollarOpens b))] with z hz
      simp only [hz,Pi.zero_apply,zero_mul]
    exact hEq.trans hIntegral.symm
  have hAll := native_energy_equation_of_forall_testFunction
    (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
    (memLp_identityEnergyIntegrand (radiusTwoCollarOpens b))
    (0 : Lp ℝ 2 ((volume : Measure R3).restrict (radiusTwoCollarOpens b)))
    (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens b) (w : RadiusTwoH1)) hCompact v
  simpa only [dirichletForcing_apply,inner_zero_left] using hAll

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoCommonRow_cutoff_collar_weak_equation
