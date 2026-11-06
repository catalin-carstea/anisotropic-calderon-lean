import Calderon.SmoothSobolevBridge
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge
set_option trace.profiler false
set_option maxHeartbeats 200000
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Actual affine Lax–Milgram forcing on the existing zero-boundary Sobolev subspace. -/
def affineDirichletForcing (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x) ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))
      ⊤ ((volume : Measure R3).restrict ballOpens)) : StrongDual ℝ BallH1Zero :=
  -((TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens) hcoeff (smoothSobolev f)).comp
    (TauCeti.w1p0Submodule volume ballOpens 2).toSubmodule.subtypeL)

@[simp] theorem affineDirichletForcing_apply (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x) ((0 : R3 → R3) x) ((0 : R3 → ℝ) x))
      ⊤ ((volume : Measure R3).restrict ballOpens)) (v : BallH1Zero) :
    affineDirichletForcing g f hcoeff v =
      -TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0 (smoothSobolev f) (v : BallH1) := by
  simp only [affineDirichletForcing, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact congrArg Neg.neg (TauCeti.PDE.energyFormH1L_apply hcoeff _ _)

end OAI.AnisotropicCalderon.EnergyBridge

#print axioms OAI.AnisotropicCalderon.EnergyBridge.affineDirichletForcing_apply
