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

def referencePrincipalMultiplierFamily (hcalc : FixedSobolevCalculus) (i j : Fin 3) :
    (ℝ × (R3 × ℝ)) → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
  let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  let F : (ℝ × (R3 × ℝ)) → SmoothCoefficientMatrix 1 :=
    commonSupportMatrixFamily 1 a h.1 K hK h.2.2.2.1
  fun p => coefficientMultiplier hcalc 0 (F p i j)

theorem contDiff_referencePrincipalMultiplierFamily (hcalc : FixedSobolevCalculus)
    (i j : Fin 3) :
    ContDiff ℝ ∞ (referencePrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc i j) := by
  let h := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  let K : Set R3 := closedBall (0 : R3) 3
  let hK : IsCompact K := isCompact_closedBall _ _
  have hM := contDiff_commonSupport_actual_coefficientMultiplier hcalc 0
    (fun t => a t i j) (contDiff_pi.mp (contDiff_pi.mp h.1 i) j) K hK
    (fun t z hz => by rw [h.2.2.2.1 t z hz]; rfl)
  simpa only [referencePrincipalMultiplierFamily, commonSupportMatrixFamily,
    commonSupportCoefficientMatrix, real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] using hM

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
