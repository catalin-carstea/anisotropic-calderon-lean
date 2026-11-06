import Calderon.NativeSobolevCoordinateDerivativeCoherence
import Calderon.InheritedNormedStructureData

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
NATIVE-LOWER-ORDER-WRAPPER-EXPANSION-v001.md. The same Tau lowering in the native graph norm. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge DriftBootstrap

def nativeLowerOrderL (k : ℕ) : BallSobolev (k+1) →L[ℝ] BallSobolev k := by
  let L : BallSobolev (k+1) →ₗ[ℝ] BallSobolev k :=
    { toFun := TauCeti.Wkp.lowerOrder (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := 2) k
      map_add' := fun U V =>
        (TauCeti.Wkp.lowerOrderL (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) k).map_add U V
      map_smul' := fun c U => by
        have hm := (TauCeti.Wkp.lowerOrderL (mu := (volume : Measure R3))
          (Omega := ballOpens) (p := 2) k).map_smul c U
        simpa only [RingHom.id_apply,TauCeti.Wkp.lowerOrder,
          real_nontriviallyNormedField_normedField_eq,
          submodule_normedSpace_module_eq] using hm }
  exact L.mkContinuous 1 (fun U => by
    have hLU : L U = TauCeti.Wkp.lowerOrder (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := 2) k U := rfl
    rw [hLU,one_mul]
    exact TauCeti.Wkp.norm_lowerOrder_le k U)

lemma nativeLowerOrderL_apply (k : ℕ) (U : BallSobolev (k+1)) :
    nativeLowerOrderL k U = TauCeti.Wkp.lowerOrder k U := rfl

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeLowerOrderL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.nativeLowerOrderL_apply
