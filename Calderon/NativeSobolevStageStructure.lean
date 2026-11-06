import Calderon.NativeStrongDirichletInverseForcingComposition

/-! The stored native graph structures, with no stage expansion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

lemma nativeSobolevSucc_normedAddCommGroup_eq_stage (k : ℕ) :
    TauCeti.Wkp.instNormedAddCommGroup (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (k+1) =
      TauCeti.SobolevStage.instNormedAddCommGroup (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k := rfl

lemma nativeSobolevSucc_normedSpace_eq_stage (k : ℕ) :
    TauCeti.Wkp.instNormedSpace (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) (k+1) =
      TauCeti.SobolevStage.instNormedSpace (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2) k := rfl

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeSobolevSucc_normedAddCommGroup_eq_stage
#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeSobolevSucc_normedSpace_eq_stage
