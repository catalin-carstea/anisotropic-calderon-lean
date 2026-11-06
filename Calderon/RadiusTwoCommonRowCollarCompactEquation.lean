import Calderon.RadiusTwoCommonRowOffPoleWeakEquation
import Calderon.NativeCompactTestDomainEnlargement
import Calderon.NativeNestedExtendedZeroEnergyDiagnostic
import Calderon.RadiusTwoEuclideanCollar

/-! EXPANSION.json precedes the derived SAME-K actual collar equation. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Metric Filter TopologicalSpace
open scoped ENNReal Distributions ContDiff Topology
namespace OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
open EnergyBridge TauCeti TauCeti.PDE
attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

theorem radiusTwoCommonRow_cutoff_collar_compact_equation
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
    (phi : 𝓓(radiusTwoCollarOpens b, ℝ)) :
    energyFormH1 (fun _ : R3 => (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (0 : R3 → R3) (0 : R3 → ℝ)
      (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens b) (w : RadiusTwoH1))
      (nativeZeroTestLinear (radiusTwoCollarOpens b) phi :
        W1p (volume : Measure R3) (radiusTwoCollarOpens b) 2) = 0 := by
  let Phi : 𝓓(radiusTwoOpens, ℝ) := TestFunction.monoCLM ℝ phi
  have hPhi : (Phi : R3 → ℝ) = (phi : R3 → ℝ) :=
    testFunction_monoCLM_coe_of_le (radiusTwoCollarOpens b) radiusTwoOpens
      (radiusTwoCollarOpens_le_radiusTwoOpens b) phi
  have hSupport : tsupport (Phi : R3 → ℝ) ⊆ (radiusTwoCollarOpens b : Set R3) := by
    intro z hz
    rw [hPhi] at hz
    exact phi.tsupport_subset hz
  have hPhiOne : ∀ z ∈ tsupport (Phi : R3 → ℝ), chi z = 1 :=
    fun z hz => hOne z (hSupport hz)
  have hPhiPole : (2 : ℝ) • q ∉ tsupport (Phi : R3 → ℝ) := by
    intro hp
    exact (not_lt_of_ge hPole) (hSupport hp).1
  have hN := radiusTwoCommonRow_cutoff_offpole_weak_equation
    g hg a ha ha1 q hq K hLimit chi w hValue Phi hPhiOne hPhiPole
  have hExt := nativeZeroTestLinear_extendByZeroL_eq_mono
    (radiusTwoCollarOpens b) radiusTwoOpens (radiusTwoCollarOpens_le_radiusTwoOpens b) phi
  have hTestEnergy := congrArg
    (fun v : RadiusTwoH1 => energyFormH1 (principalCoefficient g)
      (0 : R3 → R3) (0 : R3 → ℝ) (w : RadiusTwoH1) v) hExt
  have hNested := EnergyBridge.NativeNestedDomain.energyFormH1_extendedZeroTest_eq_restriction
    (radiusTwoCollarOpens b) radiusTwoOpens (radiusTwoCollarOpens_le_radiusTwoOpens b)
    (principalCoefficient g) (memLp_radiusTwoMetricEnergyIntegrand g hg)
    (w : RadiusTwoH1) (nativeZeroTestLinear (radiusTwoCollarOpens b) phi)
  have hSmall := hNested.symm.trans (hTestEnergy.trans hN)
  have hIdentity := nativeMetricEnergy_eq_identity_on_radiusTwoCollar g hg b hb
    (W1p.restrictL (radiusTwoCollarOpens_le_radiusTwoOpens b) (w : RadiusTwoH1))
    (nativeZeroTestLinear (radiusTwoCollarOpens b) phi :
      W1p (volume : Measure R3) (radiusTwoCollarOpens b) 2)
  exact hIdentity.symm.trans hSmall

end OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier
#print axioms OAI.AnisotropicCalderon.ExteriorSource.BoundaryBarrier.radiusTwoCommonRow_cutoff_collar_compact_equation
