import Calderon.AffineForcing

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

section GenericDomain
variable {ι : Type*} [Fintype ι]
variable {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
variable {Omega : TopologicalSpace.Opens (EuclideanSpace ℝ ι)}
variable {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}

def tauAffineForcing
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega))
    (d : TauCeti.W1p mu Omega 2) : StrongDual ℝ (TauCeti.W1p0 mu Omega 2) :=
  -((TauCeti.PDE.energyFormH1L (mu := mu) (Omega := Omega) hcoeff d).comp
    (TauCeti.w1p0Submodule mu Omega 2).toSubmodule.subtypeL)

def tauAffineCorrection
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega))
    (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := mu) (Omega := Omega) hcoeff))
    (d : TauCeti.W1p mu Omega 2) : TauCeti.W1p0 mu Omega 2 :=
  hco.solutionOfFunctional (tauAffineForcing hcoeff d)

theorem tauAffineCorrection_equation
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega))
    (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := mu) (Omega := Omega) hcoeff))
    (d : TauCeti.W1p mu Omega 2) (v : TauCeti.W1p0 mu Omega 2) :
    TauCeti.PDE.energyFormH1L0 (mu := mu) (Omega := Omega) hcoeff
      (tauAffineCorrection hcoeff hco d) v =
      -TauCeti.PDE.energyFormH1L (mu := mu) (Omega := Omega) hcoeff d
        (v : TauCeti.W1p mu Omega 2) := by
  exact (hco.apply_solutionOfFunctional_eq (tauAffineForcing hcoeff d) v).trans
    (by simp only [tauAffineForcing, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply])

end GenericDomain
end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineCorrection_equation
