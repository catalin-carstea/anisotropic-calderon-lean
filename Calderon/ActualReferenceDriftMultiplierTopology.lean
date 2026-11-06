import Calderon.ActualJointReferenceCoefficientData
import Calderon.CoordinateFluxEnergy
import Calderon.ClosedCoefficientMultiplier
import Calderon.ParametricWeightedForcing
import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.FiniteForcingEnergy
import Calderon.NativeFiniteForcingEnergyTopology
import Calderon.ActualReferenceWeakEnergyDecomposition
import Calderon.ActualReferenceFiniteForcingFamily
import Calderon.InheritedNormedStructureData
import Calderon.LpInheritedStructureData
import Calderon.ClmInheritedStructureData

/-! Exact diagnostic partition of immutable weak-energy efd9; declaration blocks/context unchanged. Parent checking pending. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
private abbrev nativeStrongDualNormedAddCommGroup :
    NormedAddCommGroup (StrongDual ℝ BallH1Zero) :=
  NormedAddCommGroup.ofSeparation (fun (f : StrongDual ℝ BallH1Zero) (hf : ‖f‖ = 0) => by
    apply ContinuousLinearMap.ext
    intro v
    change f v = 0
    apply norm_le_zero_iff.mp
    calc
      ‖f v‖ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
      _ = 0 := by rw [hf, zero_mul])

attribute [local instance] nativeStrongDualNormedAddCommGroup

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

def referenceDriftMultiplierFamily (hcalc : FixedSobolevCalculus) (i : Fin 3) :
    (ℝ × (R3 × ℝ)) → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  let G : Fin 3 → (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 1 := fun j =>
    commonSupportCoefficientFamily 1
      (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t j)
      ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp hc.1) K hK
      (fun t z hz => by rw [hc.2 t z hz]; rfl)
  fun p => coefficientMultiplier hcalc 0 (G i p)

theorem contDiff_referenceDriftMultiplierFamily (hcalc : FixedSobolevCalculus)
    (i : Fin 3) :
    ContDiff ℝ ∞ (referenceDriftMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc i) := by
  let hc := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  have hMc := contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
    (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t i)
    ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp hc.1) K hK
    (fun t z hz => by rw [hc.2 t z hz]; rfl)
  simpa only [referenceDriftMultiplierFamily, real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] using hMc

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
