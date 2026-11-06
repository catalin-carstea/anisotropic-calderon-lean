import Calderon.UnitBallContinuousCoefficientLp
import Calderon.UnitBallCoefficientOperatorSignature
import Calderon.TypedCoefficientEnergyCurveContinuity

/-! Full upfront: EXPANSION.json. Typed same-energy six-root construction; raw Tau operator Eq remains open.
Compact uniform coefficient convergence gives literal native operator norm continuity. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Matrix.Norms.Elementwise ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem continuous_dilatedCoefficientEnergyIntegrand_joint
    (A : MatrixField) (hA : Continuous A) :
    Continuous (fun p : ℝ × R3 => TauCeti.PDE.energyIntegrand
      (A (p.1 • p.2)) (0 : R3) (0 : ℝ)) :=
  TauCeti.PDE.Continuous.energyIntegrand
    (hA.comp (continuous_fst.smul continuous_snd)) continuous_const continuous_const

def dilatedCoefficientEnergyLp (A : MatrixField) (hA : Continuous A) (R : ℝ) :
    Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
  unitBallContinuousFieldLp
    (fun R x => TauCeti.PDE.energyIntegrand (A (R • x)) (0 : R3) (0 : ℝ))
    (continuous_dilatedCoefficientEnergyIntegrand_joint A hA) R

theorem continuous_dilatedCoefficientEnergyLp (A : MatrixField) (hA : Continuous A) :
    Continuous (dilatedCoefficientEnergyLp A hA) := by
  have hh := continuous_unitBallContinuousFieldLp
    (V := ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ))
  try simp only [real_nontriviallyNormedField_normedField_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq, clm_normedSpace_module_eq] at hh
  exact hh _ (continuous_dilatedCoefficientEnergyIntegrand_joint A hA)

def dilatedCoefficientNativeEnergy (A : MatrixField) (hA : Continuous A) (R : ℝ) :
    BallH1Zero →L[ℝ] BallH1Zero →L[ℝ] ℝ :=
  unitBallCoefficientEnergyL (dilatedCoefficientEnergyLp A hA R)

theorem continuous_dilatedCoefficientNativeEnergy (A : MatrixField) (hA : Continuous A) :
    Continuous (dilatedCoefficientNativeEnergy A hA) :=
  continuous_unitBallCoefficientEnergyL_curve (dilatedCoefficientEnergyLp A hA)
    (continuous_dilatedCoefficientEnergyLp A hA)

theorem tendsto_dilatedCoefficientNativeEnergy_one (A : MatrixField) (hA : Continuous A) :
    Tendsto (dilatedCoefficientNativeEnergy A hA) (𝓝 (1 : ℝ))
      (𝓝 (dilatedCoefficientNativeEnergy A hA 1)) :=
  (continuous_dilatedCoefficientNativeEnergy A hA).continuousAt

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_dilatedCoefficientEnergyIntegrand_joint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dilatedCoefficientEnergyLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_dilatedCoefficientEnergyLp
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.dilatedCoefficientNativeEnergy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.continuous_dilatedCoefficientNativeEnergy
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.tendsto_dilatedCoefficientNativeEnergy_one
