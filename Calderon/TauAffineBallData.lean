import Calderon.TauAffineData
import Calderon.TauAffineBall

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

variable (g : MatrixField)
variable (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x)
  ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤ ((volume : Measure R3).restrict ballOpens))
variable (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
  (Omega := ballOpens) hcoeff))

theorem affineDirichletSolution_add (f h : SmoothData) :
    affineDirichletSolution g ⟨f.1 + h.1, f.2.add h.2⟩ hcoeff hco =
      affineDirichletSolution g f hcoeff hco + affineDirichletSolution g h hcoeff hco := by
  change tauAffineSolution hcoeff hco (smoothSobolev ⟨f.1 + h.1, f.2.add h.2⟩) =
    tauAffineSolution hcoeff hco (smoothSobolev f) +
      tauAffineSolution hcoeff hco (smoothSobolev h)
  rw [smoothSobolev_add]
  exact tauAffineSolution_add hcoeff hco _ _

theorem eq_affineDirichletSolution (f : SmoothData) (U : BallH1)
    (haff : U - smoothSobolev f ∈ TauCeti.w1p0Submodule volume ballOpens 2)
    (horth : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 U (v : BallH1) = 0) :
    U = affineDirichletSolution g f hcoeff hco :=
  tauAffineSolution_eq_of_affine_orthogonal hcoeff hco (smoothSobolev f) U haff horth

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.affineDirichletSolution_add
#print axioms OAI.AnisotropicCalderon.EnergyBridge.eq_affineDirichletSolution
