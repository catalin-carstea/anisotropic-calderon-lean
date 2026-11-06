import Calderon.TauAffineAlgebra

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

def affineDirichletCorrection (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) hcoeff)) : BallH1Zero :=
  tauAffineCorrection (mu := (volume : Measure R3)) (Omega := ballOpens)
    hcoeff hco (smoothSobolev f)

def affineDirichletSolution (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) hcoeff)) : BallH1 :=
  tauAffineSolution (mu := (volume : Measure R3)) (Omega := ballOpens)
    hcoeff hco (smoothSobolev f)

theorem energyForm_affineDirichletSolution_zero (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) hcoeff)) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
      (affineDirichletSolution g f hcoeff hco) (v : BallH1) = 0 :=
  tauAffineSolution_orthogonal hcoeff hco (smoothSobolev f) v

theorem affineSobolevEnergy_min (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) hcoeff))
    (hsymm : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, (principalCoefficient g x).IsSymm)
    (v : BallH1Zero) :
    affineSobolevEnergy g f (affineDirichletCorrection g f hcoeff hco : BallH1) ≤
      affineSobolevEnergy g f (v : BallH1) :=
  tauAffineSolution_min hcoeff hco hsymm (smoothSobolev f) v

theorem minimalEnergy_eq_affineDirichletSolution_energy
    (hzero : SmoothBoundaryZeroClosure) (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x)
      ((0 : R3 → R3) x) ((0 : R3 → ℝ) x)) ⊤ ((volume : Measure R3).restrict ballOpens))
    (hco : IsCoercive (TauCeti.PDE.energyFormH1L0 (mu := (volume : Measure R3))
      (Omega := ballOpens) hcoeff))
    (hsymm : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, (principalCoefficient g x).IsSymm) :
    minimalEnergy g f.1 = TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
      (affineDirichletSolution g f hcoeff hco)
      (affineDirichletSolution g f hcoeff hco) := by
  have hb : BddBelow (affineSobolevEnergy g f ''
      (TauCeti.w1p0Submodule volume ballOpens 2 : Set BallH1)) := by
    refine ⟨affineSobolevEnergy g f (affineDirichletCorrection g f hcoeff hco : BallH1), ?_⟩
    rintro y ⟨v, hv, rfl⟩
    exact affineSobolevEnergy_min g f hcoeff hco hsymm ⟨v, hv⟩
  rw [minimalEnergy_eq_sInf_affineSobolevEnergy hzero g f hcoeff hb]
  change sInf _ = affineSobolevEnergy g f
    (affineDirichletCorrection g f hcoeff hco : BallH1)
  apply le_antisymm
  · exact csInf_le hb ⟨_, (affineDirichletCorrection g f hcoeff hco).2, rfl⟩
  · apply le_csInf
      (Set.Nonempty.image _ ⟨_, (affineDirichletCorrection g f hcoeff hco).2⟩)
    rintro y ⟨v, hv, rfl⟩
    exact affineSobolevEnergy_min g f hcoeff hco hsymm ⟨v, hv⟩

end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.energyForm_affineDirichletSolution_zero
#print axioms OAI.AnisotropicCalderon.EnergyBridge.affineSobolevEnergy_min
#print axioms OAI.AnisotropicCalderon.EnergyBridge.minimalEnergy_eq_affineDirichletSolution_energy
