import Calderon.TauAffineAlgebra
import Calderon.CoerciveFunctionalSolverZero
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

/-! EXPANSION.json precedes generic actual inverse-zero and affine consequences. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
section GenericDomain
variable {ι : Type*} [Fintype ι]
variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
variable {Omega : TopologicalSpace.Opens (EuclideanSpace ℝ ι)}
variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
variable (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
    ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
    ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega))

variable (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := mu) (Omega := Omega) hcoeff))

lemma tauAffineCorrection_eq_zero_of_forcing_eq_zero (d : TauCeti.W1p mu Omega 2)
    (hForce : tauAffineForcing hcoeff d = 0) : tauAffineCorrection hcoeff hco d = 0 := by
  have hZeroGen := ExteriorSource.solutionOfFunctional_zero
    (V := TauCeti.W1p0 mu Omega 2)
  try simp only [real_nontriviallyNormedField_normedField_eq,
    submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
    clm_normedAddCommGroup_seminormedAddCommGroup_eq,
    normedAddCommGroup_ofSeparation_eq,
    submodule_seminormedAddCommGroup_topologicalSpace_eq,
    submodule_seminormedAddCommGroup_addCommMonoid_eq,
    submodule_normedSpace_module_eq,
    lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
    clm_seminormedAddCommGroup_topologicalSpace_eq,
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hZeroGen
  have hZero : hco.solutionOfFunctional (0 : StrongDual ℝ (TauCeti.W1p0 mu Omega 2)) = 0 :=
    hZeroGen (TauCeti.PDE.energyFormH1L0 (mu := mu) (Omega := Omega) hcoeff) hco
  have hApply := congrArg
    (fun ell : StrongDual ℝ (TauCeti.W1p0 mu Omega 2) => hco.solutionOfFunctional ell) hForce
  exact hApply.trans hZero

lemma tauAffineSolution_eq_self_of_forcing_eq_zero (d : TauCeti.W1p mu Omega 2)
    (hForce : tauAffineForcing hcoeff d = 0) : tauAffineSolution hcoeff hco d = d := by
  have hCorr := tauAffineCorrection_eq_zero_of_forcing_eq_zero hcoeff hco d hForce
  have hAdd := congrArg (fun w : TauCeti.W1p0 mu Omega 2 =>
    d + (w : TauCeti.W1p mu Omega 2)) hCorr
  exact hAdd.trans (add_zero d)

end GenericDomain
end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineCorrection_eq_zero_of_forcing_eq_zero
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineSolution_eq_self_of_forcing_eq_zero
