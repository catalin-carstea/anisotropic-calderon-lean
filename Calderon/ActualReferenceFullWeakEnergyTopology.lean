import Calderon.ActualReferenceFullWeakEnergy
import Calderon.ActualReferencePrincipalMultiplierTopology
import Calderon.ActualReferenceDriftMultiplierTopology

/-! Full upfront argument: EXPANSION-actual-reference-weak-endpoint-joint-topology-v001.json.
Actual joint families, author draft awaiting checks. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


theorem contDiff_referenceFullWeakEnergyFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) := by
  let J : BallH1 →L[ℝ] BallH1 := ContinuousLinearMap.id ℝ BallH1
  let V : BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)
  have ht := contDiff_finiteForcingEnergy J unitBallCoordinateGradientL V
    (referencePrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc)
    (referenceDriftMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc)
    (contDiff_referencePrincipalMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc)
    (contDiff_referenceDriftMultiplierFamily g L y0 Φ B ε C ρ H a w hData hcalc)
  change ContDiff ℝ ∞ (fun p : ℝ × (R3 × ℝ) =>
    referenceFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
  unfold referenceFullWeakEnergyFamily
  simpa only [referenceFullWeakEnergyFamily, referencePrincipalMultiplierFamily,
    referenceDriftMultiplierFamily, J, V,
    real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] using ht

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceFullWeakEnergyFamily
