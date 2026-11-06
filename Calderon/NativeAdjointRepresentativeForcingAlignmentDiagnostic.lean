import Calderon.NativeCoefficientWeakHalfLift
import Calderon.NativeSupportedAdjointH2Inverse

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL

lemma nativeWeakEnergy_forcing_of_isWeakSolution
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hc : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) (f : BallSobolev 0) (u : BallH1Zero)
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens) a b c f u)
    (v : BallH1Zero) :
    nativeCoefficientWeakEnergyL a b c hc (u : BallH1) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v := by
  have he : nativeCoefficientWeakEnergyL a b c hc (u : BallH1) v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a b c (u : BallH1) (v : BallH1) := nativeCoefficientWeakEnergyL_apply a b c hc (u : BallH1) v
  exact he.trans (hu v)

lemma nativeWeakEnergy_strongRepresentative_forcing
    (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hc : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) (c x)) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (R : BallSobolev 0 →L[ℝ] StrongDirichletSpace 0)
    (hR : ∀ f : BallSobolev 0, TauCeti.PDE.IsWeakSolutionDirichlet
      (mu := (volume : Measure R3)) (Omega := ballOpens) a b c f (strongDirichletProjectionL 0 (R f)))
    (f : BallSobolev 0) (v : BallH1Zero) :
    nativeCoefficientWeakEnergyL a b c hc (strongDirichletProjectionL 0 (R f) : BallH1) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v := by
  exact nativeWeakEnergy_forcing_of_isWeakSolution a b c hc f (strongDirichletProjectionL 0 (R f)) (hR f) v

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakEnergy_forcing_of_isWeakSolution
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeWeakEnergy_strongRepresentative_forcing
