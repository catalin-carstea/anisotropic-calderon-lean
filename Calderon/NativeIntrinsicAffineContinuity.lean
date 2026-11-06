import Calderon.NativeIntrinsicAffineCorrectionContinuity

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

lemma continuous_tauAffineSolution :
    Continuous (fun d : TauCeti.W1p mu Omega 2 => tauAffineSolution hcoeff hco d) := by
  unfold tauAffineSolution
  exact continuous_id.add
    (continuous_subtype_val.comp (continuous_tauAffineCorrection hcoeff hco))

end GenericDomain
end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.continuous_tauAffineSolution
