import Calderon.RadiusTwoCommonRowLocalizedCompactEquation
import Calderon.RadiusTwoNativeSourceSolution

/-! EXPANSION.json precedes actual localized row identification with the EXISTING solver. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Distributions Gradient InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem radiusTwoCommonRow_localized_eq_sourceSolution
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (q : R3) (hq : q ∈ ball (0 : R3) a)
    (K : RadiusTwoL2)
    (hLimit : Tendsto (fun n : ℕ => TauCeti.W1p.value
      (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing
        ⟨radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n,
          (radiusTwoCommonNormalizedDeltaSequence a ha ha1 q hq n).contDiff⟩) : RadiusTwoH1))
      atTop (𝓝 K))
    (χ : R3 → ℝ) (w : RadiusTwoH1Zero)
    (hValue : (TauCeti.W1p.value (w : RadiusTwoH1) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict radiusTwoOpens] (fun z : R3 => χ z * K z))
    (η : 𝓓(radiusTwoOpens, ℝ))
    (hOne : ∀ z ∈ tsupport (η : R3 → ℝ), χ z = 1)
    (hPole : (2 : ℝ) • q ∉ tsupport (η : R3 → ℝ))
    {M : ℝ} (hM : 0 ≤ M)
    (hAbs : ∀ x ∈ (radiusTwoOpens : Set R3), |η x| ≤ M)
    (hGrad : ∀ x ∈ (radiusTwoOpens : Set R3), ‖gradient (η : R3 → ℝ) x‖ ≤ M) :
    TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad (w : RadiusTwoH1) =
      (radiusTwoSourceSolution g hg
        (radiusTwoFixedRowCutoffForcingLp g hg ⟨η,η.contDiff⟩ (w : RadiusTwoH1)) : RadiusTwoH1) := by
  let ηData : SmoothData := ⟨η,η.contDiff⟩
  let S : RadiusTwoH1 →L[ℝ] RadiusTwoH1 :=
    TauCeti.W1p.contDiffSMulL (η : R3 → ℝ) η.contDiff hM hAbs hGrad
  let f : RadiusTwoL2 := radiusTwoFixedRowCutoffForcingLp g hg ηData (w : RadiusTwoH1)
  have hMem : S (w : RadiusTwoH1) ∈ TauCeti.w1p0Submodule (volume : Measure R3) radiusTwoOpens 2 :=
    TauCeti.W1p.contDiffSMul_mem_w1p0Submodule η.contDiff hM hAbs hGrad w.property
  let z : RadiusTwoH1Zero := ⟨S (w : RadiusTwoH1),hMem⟩
  have hWeak : TauCeti.PDE.IsWeakSolutionDirichlet
      (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ) f z := by
    apply (TauCeti.PDE.isWeakSolutionDirichlet_iff_forall_testFunction
      (memLp_radiusTwoMetricEnergyIntegrand g hg) f z).mpr
    intro φ
    have hCompact := radiusTwoCommonRow_localized_compactTest_equation
      g hg a ha ha1 q hq K hLimit χ w hValue η hOne hPole hM hAbs hGrad φ
    change TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
      (S (w : RadiusTwoH1)) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) =
      ∫ x in radiusTwoOpens, f x * φ x ∂(volume : Measure R3) at hCompact
    have hNative :
        TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
          (S (w : RadiusTwoH1)) (TauCeti.W1p.ofTestFunctionₗ volume radiusTwoOpens 2 φ) =
        TauCeti.PDE.energyFormH1 (principalCoefficient g) (0 : R3 → R3) (0 : R3 → ℝ)
          (S (w : RadiusTwoH1)) (nativeZeroTestLinear radiusTwoOpens φ : RadiusTwoH1) :=
      congrArg (fun v : RadiusTwoH1 => TauCeti.PDE.energyFormH1 (principalCoefficient g)
        (0 : R3 → R3) (0 : R3 → ℝ) (S (w : RadiusTwoH1)) v)
        (nativeZeroTestLinear_coe radiusTwoOpens φ).symm
    exact hNative.trans hCompact
  have hIdentity : z = radiusTwoSourceSolution g hg f := eq_radiusTwoSourceSolution g hg f z hWeak
  exact congrArg (fun v : RadiusTwoH1Zero => (v : RadiusTwoH1)) hIdentity


end OAI.AnisotropicCalderon.ExteriorSource
