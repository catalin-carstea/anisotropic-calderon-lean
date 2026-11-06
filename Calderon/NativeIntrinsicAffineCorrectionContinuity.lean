import Calderon.TauAffineAlgebra
import Calderon.ContinuousFunctionalSolverDiagnostic
import Calderon.NativeAffineForcingPostcomposition
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

/-! EXPANSION.json precedes this exact intrinsic1+1 continuity partition. -/
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

lemma continuous_tauAffineCorrection :
    Continuous (fun d : TauCeti.W1p mu Omega 2 => tauAffineCorrection hcoeff hco d) := by
  have hInvGen := ExteriorSource.continuous_solutionOfFunctional
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
    clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hInvGen
  have hInv : Continuous (fun ell : StrongDual ℝ (TauCeti.W1p0 mu Omega 2) =>
      hco.solutionOfFunctional ell) :=
    hInvGen (TauCeti.PDE.energyFormH1L0 (mu := mu) (Omega := Omega) hcoeff) hco
  have hComp : Continuous (fun d : TauCeti.W1p mu Omega 2 =>
      hco.solutionOfFunctional (tauAffineForcing hcoeff d)) :=
    continuous_tauAffineForcing_postcomp hcoeff
      (fun ell : StrongDual ℝ (TauCeti.W1p0 mu Omega 2) => hco.solutionOfFunctional ell) hInv
  unfold tauAffineCorrection
  exact hComp


end GenericDomain
end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.continuous_tauAffineCorrection
