import Calderon.WeightedRadialDriftCoercivity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def weightedDriftSlice (w : (R3 × ℝ) × R3 → ℝ)
    (b : (R3 × ℝ) × R3 → R3) (L : ℝ) (p : R3 × ℝ) : R3 → R3 :=
  fun z => weightedLinearRadialDrift w b L (p, z)

theorem contDiff_weightedDriftSlice (w : (R3 × ℝ) × R3 → ℝ)
    (hw : ContDiff ℝ ∞ w) (b : (R3 × ℝ) × R3 → R3)
    (hb : ContDiff ℝ ∞ b) (L : ℝ) (p : R3 × ℝ) :
    ContDiff ℝ ∞ (weightedDriftSlice w b L p) :=
  (contDiff_weightedLinearRadialDrift w hw b hb L).comp
    (contDiff_const.prodMk contDiff_id)

theorem weightedDriftSlice_support (w : (R3 × ℝ) × R3 → ℝ)
    (b : (R3 × ℝ) × R3 → R3) (L : ℝ) (p : R3 × ℝ) (K : Set R3)
    (hz : ∀ p z, z ∉ K → w (p,z) = 0) :
    ∀ z, z ∉ K → weightedDriftSlice w b L p z = 0 := by
  intro z h
  simp [weightedDriftSlice, weightedLinearRadialDrift, hz p z h]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
