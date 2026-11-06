import Calderon.TauAffine

/-! EXPANSION.json precedes this intrinsic actual native forcing continuity leaf. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma continuous_tauAffineForcing {ι : Type*} [Fintype ι]
    {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
    {Omega : TopologicalSpace.Opens (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega)) :
    Continuous (fun d : TauCeti.W1p mu Omega 2 => tauAffineForcing hcoeff d) := by
  unfold tauAffineForcing
  exact ((TauCeti.PDE.energyFormH1L (mu := mu) (Omega := Omega) hcoeff).continuous.clm_comp
    (continuous_const : Continuous (fun _ : TauCeti.W1p mu Omega 2 =>
      (TauCeti.w1p0Submodule mu Omega 2).toSubmodule.subtypeL))).neg

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.continuous_tauAffineForcing
