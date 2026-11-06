import Calderon.TauAffineAlgebra

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
variable (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := mu) (Omega := Omega) hcoeff))

theorem tauAffineCorrection_eq_of_equation (d : TauCeti.W1p mu Omega 2)
    (w : TauCeti.W1p0 mu Omega 2)
    (hw : ∀ v : TauCeti.W1p0 mu Omega 2,
      TauCeti.PDE.energyFormH1L0 (mu := mu) (Omega := Omega) hcoeff w v =
      -TauCeti.PDE.energyFormH1L (mu := mu) (Omega := Omega) hcoeff d
        (v : TauCeti.W1p mu Omega 2)) :
    w = tauAffineCorrection hcoeff hco d := by
  apply hco.eq_solutionOfFunctional
  intro v
  rw [hw]
  simp only [tauAffineForcing, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]

theorem tauAffineCorrection_add (d₁ d₂ : TauCeti.W1p mu Omega 2) :
    tauAffineCorrection hcoeff hco (d₁ + d₂) =
      tauAffineCorrection hcoeff hco d₁ + tauAffineCorrection hcoeff hco d₂ := by
  apply (tauAffineCorrection_eq_of_equation hcoeff hco (d₁ + d₂)
    (tauAffineCorrection hcoeff hco d₁ + tauAffineCorrection hcoeff hco d₂) ?_).symm
  intro v
  rw [map_add, ContinuousLinearMap.add_apply,
    tauAffineCorrection_equation hcoeff hco d₁,
    tauAffineCorrection_equation hcoeff hco d₂]
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

theorem tauAffineSolution_add (d₁ d₂ : TauCeti.W1p mu Omega 2) :
    tauAffineSolution hcoeff hco (d₁ + d₂) =
      tauAffineSolution hcoeff hco d₁ + tauAffineSolution hcoeff hco d₂ := by
  simp only [tauAffineSolution, tauAffineCorrection_add, Submodule.coe_add]
  abel

theorem tauAffineSolution_eq_of_affine_orthogonal
    (d U : TauCeti.W1p mu Omega 2)
    (haff : U - d ∈ TauCeti.w1p0Submodule mu Omega 2)
    (horth : ∀ v : TauCeti.W1p0 mu Omega 2,
      TauCeti.PDE.energyFormH1 a 0 0 U (v : TauCeti.W1p mu Omega 2) = 0) :
    U = tauAffineSolution hcoeff hco d := by
  let w : TauCeti.W1p0 mu Omega 2 := ⟨U - d, haff⟩
  have hw : w = tauAffineCorrection hcoeff hco d := by
    apply tauAffineCorrection_eq_of_equation hcoeff hco d w
    intro v
    rw [TauCeti.PDE.energyFormH1L0_apply, TauCeti.PDE.energyFormH1L_apply]
    change TauCeti.PDE.energyFormH1 a 0 0 (U - d) (v : TauCeti.W1p mu Omega 2) = _
    rw [← TauCeti.PDE.energyFormH1L_apply hcoeff, map_sub,
      ContinuousLinearMap.sub_apply, TauCeti.PDE.energyFormH1L_apply, horth]
    simpa only [TauCeti.PDE.energyFormH1L_apply] using
      zero_sub (TauCeti.PDE.energyFormH1 a 0 0 d (v : TauCeti.W1p mu Omega 2))
  have he : U = d + (w : TauCeti.W1p mu Omega 2) := by
    change U = d + (U - d)
    abel
  rw [he, hw]
  rfl

end GenericDomain
end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineCorrection_eq_of_equation
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineCorrection_add
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineSolution_add
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineSolution_eq_of_affine_orthogonal
