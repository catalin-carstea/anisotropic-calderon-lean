import Calderon.TauAffineAlgebra

/-! EXPANSION.json precedes this intrinsic native affine-forcing identity. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
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
variable (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
    ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
    ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega))

lemma tauAffineForcing_apply (d : TauCeti.W1p mu Omega 2)
    (v : TauCeti.W1p0 mu Omega 2) :
    tauAffineForcing hcoeff d v =
      -TauCeti.PDE.energyFormH1 a 0 0 d (v : TauCeti.W1p mu Omega 2) := by
  unfold tauAffineForcing
  rw [ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
    TauCeti.PDE.energyFormH1L_apply]

lemma tauAffineForcing_eq_zero_of_energy_eq_zero (d : TauCeti.W1p mu Omega 2)
    (hWeak : ∀ v : TauCeti.W1p0 mu Omega 2,
      TauCeti.PDE.energyFormH1 a 0 0 d (v : TauCeti.W1p mu Omega 2) = 0) :
    tauAffineForcing hcoeff d = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  calc
    tauAffineForcing hcoeff d v =
        -TauCeti.PDE.energyFormH1 a 0 0 d (v : TauCeti.W1p mu Omega 2) :=
      tauAffineForcing_apply hcoeff d v
    _ = 0 := neg_eq_zero.mpr (hWeak v)

end GenericDomain
end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineForcing_apply
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineForcing_eq_zero_of_energy_eq_zero
