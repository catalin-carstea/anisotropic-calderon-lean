import Calderon.NativeSmoothCoefficientFullEnergy
import Calderon.NativeScalarMassFullGreen

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

def nativeSmoothCoefficientFullMassEnergyL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 1) (G : Fin 3 → SmoothCoefficientJets 1)
    (M : SmoothCoefficientJets 1) : BallH1 →L[ℝ] StrongDual ℝ BallH1 :=
  nativeSmoothCoefficientFullEnergyL hcalc F G +
    (forcingFromValueL (TauCeti.W1p.valueL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2))).comp (nativeCoefficientMassL hcalc M)

lemma nativeSmoothCoefficientFullMassEnergyL_apply (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 1) (G : Fin 3 → SmoothCoefficientJets 1)
    (M : SmoothCoefficientJets 1) (u v : BallH1) :
    nativeSmoothCoefficientFullMassEnergyL hcalc F G M u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField 1 F) (nativeSmoothDriftField G) (coefficientValue 1 M) u v := by
  have hLift : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)
  have hG : Continuous (nativeSmoothDriftField G) :=
    hLift.comp (continuous_pi (fun i => (contDiff_coefficientValue 1 (G i)).continuous))
  have hBase := memLp_nativeEnergyIntegrand_of_continuous
    (coefficientMatrixField 1 F) (nativeSmoothDriftField G) 0
    (contDiff_coefficientMatrixField 1 F).continuous hG continuous_const
  have hMass := energyFormH1_add_mass_of_native_density
    (coefficientMatrixField 1 F) (nativeSmoothDriftField G) (coefficientValue 1 M)
    hBase u v (nativeCoefficientMassL hcalc M u) (nativeCoefficientMassL_value_ae hcalc M u)
  have hBaseEval := nativeSmoothCoefficientFullEnergyL_apply hcalc F G u v
  have hMassEval := forcingFromValueL_apply_apply
    (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))
    (nativeCoefficientMassL hcalc M u) v
  change nativeSmoothCoefficientFullEnergyL hcalc F G u v +
    forcingFromValueL (TauCeti.W1p.valueL (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2)) (nativeCoefficientMassL hcalc M u) v = _
  exact (congrArg₂ (fun x y : ℝ => x+y) hBaseEval hMassEval).trans hMass.symm

lemma nativeSmoothCoefficientFullMassEnergyL_eq_energyFormH1L
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 1)
    (G : Fin 3 → SmoothCoefficientJets 1) (M : SmoothCoefficientJets 1)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (coefficientMatrixField 1 F x)
      (nativeSmoothDriftField G x) (coefficientValue 1 M x)) ⊤
      ((volume : Measure R3).restrict ballOpens)) :
    nativeSmoothCoefficientFullMassEnergyL hcalc F G M =
      TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3)) (Omega := ballOpens)
        (a := coefficientMatrixField 1 F) (b := nativeSmoothDriftField G)
        (c := coefficientValue 1 M) hcoeff := by
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  exact (nativeSmoothCoefficientFullMassEnergyL_apply hcalc F G M u v).trans
    (TauCeti.PDE.energyFormH1L_apply hcoeff u v).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothCoefficientFullMassEnergyL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothCoefficientFullMassEnergyL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSmoothCoefficientFullMassEnergyL_eq_energyFormH1L
