import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Abel

/-! Elementary endpoint product rule; the family hypotheses are discharged where it is
applied. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ConnectionError

lemma zero_hasDerivAt_normalCommutator_right_identity
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → E →L[ℝ] F) (N : ℝ → F →L[ℝ] F)
    (P W : ℝ → E →L[ℝ] E)
    (A' : E →L[ℝ] F) (N' : F →L[ℝ] F) (P' W' : E →L[ℝ] E)
    (hA : HasDerivAt A A' 0) (hN : HasDerivAt N N' 0)
    (hP : HasDerivAt P P' 0) (hW : HasDerivAt W W' 0)
    (hN0 : N 0 = ContinuousLinearMap.id ℝ F)
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hW0 : W 0 = ContinuousLinearMap.id ℝ E) :
    (((N 0).comp (A 0) - (A 0).comp (P 0)).comp (W 0) = 0) ∧
    HasDerivAt (fun r : ℝ => ((N r).comp (A r) - (A r).comp (P r)).comp (W r))
      (N'.comp (A 0) - (A 0).comp P') 0 := by
  let C : ℝ → E →L[ℝ] F := fun r => (N r).comp (A r) - (A r).comp (P r)
  have hC0 : C 0 = 0 := by
    change (N 0).comp (A 0) - (A 0).comp (P 0) = 0
    rw [hN0,hP0,ContinuousLinearMap.id_comp,ContinuousLinearMap.comp_id,sub_self]
  have hC : HasDerivAt C (N'.comp (A 0) - (A 0).comp P') 0 := by
    have h : HasDerivAt C
        (N'.comp (A 0) + (N 0).comp A' - (A'.comp (P 0) + (A 0).comp P')) 0 :=
      HasDerivAt.sub (hN.clm_comp hA) (hA.clm_comp hP)
    have hCoeff : N'.comp (A 0) + (N 0).comp A' -
        (A'.comp (P 0) + (A 0).comp P') = N'.comp (A 0) - (A 0).comp P' := by
      rw [hN0,hP0,ContinuousLinearMap.id_comp,ContinuousLinearMap.comp_id]
      abel
    rw [hCoeff] at h
    exact h
  constructor
  · change (C 0).comp (W 0) = 0
    rw [hC0,ContinuousLinearMap.zero_comp]
  · have h : HasDerivAt (fun r : ℝ => (C r).comp (W r))
        ((N'.comp (A 0) - (A 0).comp P').comp (W 0) + (C 0).comp W') 0 :=
      hC.clm_comp hW
    rw [hW0,hC0,ContinuousLinearMap.comp_id,ContinuousLinearMap.zero_comp,add_zero] at h
    exact h

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.zero_hasDerivAt_normalCommutator_right_identity
