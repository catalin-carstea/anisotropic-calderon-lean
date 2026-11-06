import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
HIGH-GENUINE-COMMUTATOR-ENDPOINT-ALGEBRA-EXPANSION-v001.md. Exact linear endpoint algebra only. -/
set_option autoImplicit false
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma highAdjointMultiplierCommutator_gain_of_endpoint_defect
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (hJinj : Function.Injective J)
    (S T : X →L[ℝ] Y) (M W K B C : X →L[ℝ] X)
    (ML : Y →L[ℝ] Y) (MN : Z →L[ℝ] Z) (D : Y →L[ℝ] Z) (c : ℝ)
    (hI : ∀ u, I (M u) = ML (I u)) (hJ : ∀ v, J (ML v) = MN (J v))
    (hWM : ∀ u, W (M u) = M (W u))
    (hB : ∀ u, I (B u) = S (M u)-ML (S u))
    (hD : ∀ u, J (T u-S u) = J (I (K u))+c • D (I (W u)))
    (hC : ∀ u, J (I (C u)) = D (ML (I u))-MN (D (I u))) (u : X) :
    I ((B+K.comp M-M.comp K+c • C.comp W) u) = T (M u)-ML (T u) := by
  have hIWM : I (W (M u)) = ML (I (W u)) :=
    (congrArg I (hWM u)).trans (hI (W u))
  have hD1 : J (T (M u))-J (S (M u)) =
      J (I (K (M u)))+c • D (ML (I (W u))) := by
    simpa only [map_sub,hIWM] using hD (M u)
  have hD2 : MN (J (T u))-MN (J (S u)) =
      MN (J (I (K u)))+c • MN (D (I (W u))) := by
    simpa only [map_sub,map_add,map_smul] using congrArg MN (hD u)
  have hB1 : J (I (B u)) = J (S (M u))-MN (J (S u)) := by
    simpa only [map_sub,hJ] using congrArg J (hB u)
  have hMK : J (I (M (K u))) = MN (J (I (K u))) :=
    (congrArg J (hI (K u))).trans (hJ (I (K u)))
  have hExpansion : J (I ((B+K.comp M-M.comp K+c • C.comp W) u)) =
      (J (S (M u))-MN (J (S u)))+J (I (K (M u)))-MN (J (I (K u)))+
        c • (D (ML (I (W u)))-MN (D (I (W u)))) := by
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,map_add,map_sub,map_smul,
      hB1,hMK,hC]
  have hAlgebra :
      (J (S (M u))-MN (J (S u)))+J (I (K (M u)))-MN (J (I (K u)))+
        c • (D (ML (I (W u)))-MN (D (I (W u)))) =
      J (T (M u))-MN (J (T u)) := by
    calc
      _ = (J (S (M u))+(J (I (K (M u)))+c • D (ML (I (W u))))) -
          (MN (J (S u))+(MN (J (I (K u)))+c • MN (D (I (W u))))) := by
            rw [smul_sub]
            abel
      _ = (J (S (M u))+(J (T (M u))-J (S (M u)))) -
          (MN (J (S u))+(MN (J (T u))-MN (J (S u)))) := by rw [← hD1,← hD2]
      _ = J (T (M u))-MN (J (T u)) := by abel
  have hTarget : J (T (M u)-ML (T u)) = J (T (M u))-MN (J (T u)) :=
    (J.map_sub _ _).trans (congrArg (fun v : Z => J (T (M u))-v) (hJ (T u)))
  exact hJinj (hExpansion.trans (hAlgebra.trans hTarget.symm))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.highAdjointMultiplierCommutator_gain_of_endpoint_defect
