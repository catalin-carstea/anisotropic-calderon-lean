import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Sigma.Basic

/-! Full before-source: weak-native-instance-repair-author-oct16-v001/
EXPANSION-boundary-full-source-data-norm-transport-v124.md. Canonical operator norm is preserved under equality of the FULL source group/space pair, not an arbitrary carrier equality. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

def normedSourceCLMCarrier (E : Type u) (F : Type v)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : Σ G : NormedAddCommGroup E,
      @NormedSpace ℝ E Real.normedField G.toSeminormedAddCommGroup) : Type (max u v) :=
  letI : NormedAddCommGroup E := d.1
  letI : NormedSpace ℝ E := d.2
  E →L[ℝ] F

def normedSourceCLMNorm (E : Type u) (F : Type v)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d : Σ G : NormedAddCommGroup E,
      @NormedSpace ℝ E Real.normedField G.toSeminormedAddCommGroup) :
    Norm (normedSourceCLMCarrier E F d) :=
  letI : NormedAddCommGroup E := d.1
  letI : NormedSpace ℝ E := d.2
  ContinuousLinearMap.hasOpNorm (E := E) (F := F) (σ₁₂ := RingHom.id ℝ)

lemma normedSourceCLMNorm_eq_of_data_eq (E : Type u) (F : Type v)
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d d' : Σ G : NormedAddCommGroup E,
      @NormedSpace ℝ E Real.normedField G.toSeminormedAddCommGroup)
    (hData : d = d') (T : normedSourceCLMCarrier E F d) :
    @norm (normedSourceCLMCarrier E F d') (normedSourceCLMNorm E F d')
        (Eq.mp (congrArg (normedSourceCLMCarrier E F) hData) T) =
      @norm (normedSourceCLMCarrier E F d) (normedSourceCLMNorm E F d) T := by
  cases hData
  rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normedSourceCLMCarrier
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normedSourceCLMNorm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.normedSourceCLMNorm_eq_of_data_eq
