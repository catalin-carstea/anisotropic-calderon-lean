import Calderon.TauAffine

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

def tauAffineSolution (d : TauCeti.W1p mu Omega 2) : TauCeti.W1p mu Omega 2 :=
  d + (tauAffineCorrection hcoeff hco d : TauCeti.W1p mu Omega 2)

theorem tauAffineSolution_orthogonal (d : TauCeti.W1p mu Omega 2)
    (v : TauCeti.W1p0 mu Omega 2) :
    TauCeti.PDE.energyFormH1 a 0 0 (tauAffineSolution hcoeff hco d)
      (v : TauCeti.W1p mu Omega 2) = 0 := by
  have hw := tauAffineCorrection_equation hcoeff hco d v
  rw [TauCeti.PDE.energyFormH1L0_apply, TauCeti.PDE.energyFormH1L_apply] at hw
  rw [tauAffineSolution, TauCeti.PDE.energyFormH1_add_left hcoeff, hw]
  exact add_neg_cancel _

theorem tauAffineSolution_quadratic_add
    (hsymm : ∀ᵐ x ∂mu.restrict Omega, (a x).IsSymm)
    (d : TauCeti.W1p mu Omega 2) (v : TauCeti.W1p0 mu Omega 2) :
    TauCeti.PDE.energyFormH1 a 0 0
      (tauAffineSolution hcoeff hco d + (v : TauCeti.W1p mu Omega 2))
      (tauAffineSolution hcoeff hco d + (v : TauCeti.W1p mu Omega 2)) =
    TauCeti.PDE.energyFormH1 a 0 0 (tauAffineSolution hcoeff hco d)
      (tauAffineSolution hcoeff hco d) +
    TauCeti.PDE.energyFormH1 a 0 0 (v : TauCeti.W1p mu Omega 2)
      (v : TauCeti.W1p mu Omega 2) := by
  have horth := tauAffineSolution_orthogonal hcoeff hco d v
  have hcross := (TauCeti.PDE.energyFormH1_comm_of_isSymm_ae (mu := mu)
    (Omega := Omega) (a := a) (c := (0 : EuclideanSpace ℝ ι → ℝ)) hsymm
    (v : TauCeti.W1p mu Omega 2) (tauAffineSolution hcoeff hco d)).trans horth
  rw [TauCeti.PDE.energyFormH1_add_left hcoeff,
    TauCeti.PDE.energyFormH1_add_right hcoeff,
    TauCeti.PDE.energyFormH1_add_right hcoeff, horth, hcross]
  ring

theorem tauAffineSolution_min
    (hsymm : ∀ᵐ x ∂mu.restrict Omega, (a x).IsSymm)
    (d : TauCeti.W1p mu Omega 2) (v : TauCeti.W1p0 mu Omega 2) :
    TauCeti.PDE.energyFormH1 a 0 0 (tauAffineSolution hcoeff hco d)
      (tauAffineSolution hcoeff hco d) ≤
    TauCeti.PDE.energyFormH1 a 0 0 (d + (v : TauCeti.W1p mu Omega 2))
      (d + (v : TauCeti.W1p mu Omega 2)) := by
  have he := tauAffineSolution_quadratic_add hcoeff hco hsymm d
    (v - tauAffineCorrection hcoeff hco d)
  have hv : tauAffineSolution hcoeff hco d +
      ((v - tauAffineCorrection hcoeff hco d : TauCeti.W1p0 mu Omega 2) :
        TauCeti.W1p mu Omega 2) = d + (v : TauCeti.W1p mu Omega 2) := by
    simp only [tauAffineSolution, Submodule.coe_sub]
    abel
  rw [hv] at he
  have hn := hco.apply_self_nonneg (v - tauAffineCorrection hcoeff hco d)
  rw [TauCeti.PDE.energyFormH1L0_apply] at hn
  rw [he]
  exact le_add_of_nonneg_right hn

end GenericDomain
end OAI.AnisotropicCalderon.EnergyBridge
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineSolution_orthogonal
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineSolution_quadratic_add
#print axioms OAI.AnisotropicCalderon.EnergyBridge.tauAffineSolution_min
