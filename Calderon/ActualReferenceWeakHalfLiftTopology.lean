import Calderon.ActualReferenceWeakHalfLift
import Calderon.ActualReferenceWeakEnergyNativeTopology
import Calderon.NativeWeakHalfLiftTopologyAlgebra
import Calderon.NativeInvertibleWeakLiftTopology
import Calderon.NativeWeakHalfLiftTopologyFactoring

/-! Full upfront argument: EXPANSION-actual-reference-weak-endpoint-joint-topology-v001.json.
Actual joint families, author draft awaiting checks. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)


theorem contDiff_joint_referenceWeakDirichletEnergyFamily (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc) := by
  have hR := contDiff_referenceWeakEnergyFamily_native
    g L y0 Φ B ε C ρ H a w hData hcalc
  have ht := contDiff_weakDirichletRestriction
    (referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc)
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    hR
  unfold referenceWeakDirichletEnergyFamily
  simpa only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] using ht


theorem referenceWeakHalfLiftFamily_eq_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) lam) :
    referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF p =
      ((ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p).inverse.comp
            (referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p))).comp
        (harmonicFirstOrderLiftCompletion hF) := by
  have ht := weakLift_formula_eq_inverse
    (referenceWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    (referenceWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc p)
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
    (harmonicFirstOrderLiftCompletion hF)
    (isCoercive_referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p lam hs)
  unfold referenceWeakHalfLiftFamily
  simpa only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq, lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] using ht


theorem contDiffAt_nativeHalfWeakLiftFormula_of_isInvertible
    (A : (ℝ × (R3 × ℝ)) → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (R : (ℝ × (R3 × ℝ)) → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero)
    (hF : SphereFischerInner) (p : ℝ × (R3 × ℝ))
    (hA : ContDiffAt ℝ ∞ A p) (hR : ContDiffAt ℝ ∞ R p)
    (hi : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun t =>
      ((ContinuousLinearMap.id ℝ BallH1) -
        (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL.comp
          ((functionalInverse (A t)).comp (R t))).comp
        (harmonicFirstOrderLiftCompletion hF)) p := by
  apply contDiffAt_nativeHalfAffineLiftFormula (hF := hF) (p := p)
  · exact contDiffAt_nativeZeroWeakFunctionalInverse_of_isInvertible A p hA hi
  · exact hR


theorem contDiffAt_referenceWeakHalfLiftFamily
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (lam : ℝ)
    (hs : UnitBallSmallDriftData (fun x => a (p,x))
      (fun x => conformalReferenceWeightedFramedDrift g L Φ H w (p,x)) lam) :
    ContDiffAt ℝ ∞ (referenceWeakHalfLiftFamily g L y0 Φ B ε C ρ H a w hData hcalc hF) p := by
  unfold referenceWeakHalfLiftFamily
  apply contDiffAt_nativeHalfWeakLiftFormula_of_isInvertible (hF := hF) (p := p)
  · exact (contDiff_joint_referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc).contDiffAt
  · exact (contDiff_referenceWeakEnergyFamily_native
      g L y0 Φ B ε C ρ H a w hData hcalc).contDiffAt
  · exact isInvertible_referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p lam hs


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_joint_referenceWeakDirichletEnergyFamily
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeakHalfLiftFamily_eq_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceWeakHalfLiftFamily
