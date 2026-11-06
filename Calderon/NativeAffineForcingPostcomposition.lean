import Calderon.NativeGenericAffineForcingContinuity

/-! EXPANSION.json precedes this pure actual native postcomposition continuity leaf. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma continuous_tauAffineForcing_postcomp {ι : Type*} [Fintype ι]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {Omega : TopologicalSpace.Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega))
    (I : StrongDual ℝ (TauCeti.W1p0 mu Omega 2) → TauCeti.W1p0 mu Omega 2)
    (hI : Continuous I) :
    Continuous (fun d : TauCeti.W1p mu Omega 2 => I (tauAffineForcing hcoeff d)) := by
  have hForce : Continuous (fun d : TauCeti.W1p mu Omega 2 => tauAffineForcing hcoeff d) :=
    continuous_tauAffineForcing hcoeff
  have hComposition : Continuous (I ∘ (fun d : TauCeti.W1p mu Omega 2 => tauAffineForcing hcoeff d)) :=
    hI.comp hForce
  exact hComposition

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.continuous_tauAffineForcing_postcomp
