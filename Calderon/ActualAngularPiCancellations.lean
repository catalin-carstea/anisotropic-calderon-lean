import Calderon.ActualAngularHighCancellation

set_option autoImplicit false
noncomputable section
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft

section Generic
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Lemma P1: `I E[a,Q] = a^h MH − ML a^h`. -/
theorem lowering_multiplier_cancellation
    (I : X →L[ℝ] Y) (Rh : Fin 3 → X →L[ℝ] Y) (Bh : X →L[ℝ] Y)
    (Mh : Fin 3 → X →L[ℝ] X) (Ml : Fin 3 → Y →L[ℝ] Y) (MH : X →L[ℝ] X) (ML : Y →L[ℝ] Y)
    (EG : Fin 3 → X →L[ℝ] X) (HQ : X →L[ℝ] X) (i : Fin 3)
    (c1 : ∀ j x, I (Mh j x) = Ml j (I x)) (c2 : ∀ j y, Ml j (ML y) = ML (Ml j y))
    (c3 : ∀ j x, Rh j (MH x) = ML (Rh j x) + I (EG j x))
    (c4 : ∀ x, I (HQ x) = Bh (MH x) - ML (Bh x)) (u : X) :
    I (((∑ j : Fin 3, (Mh j).comp (EG j)) + (Mh i).comp HQ) u) =
      ((∑ j : Fin 3, (Ml j).comp (Rh j)) + (Ml i).comp Bh) (MH u) -
        ML (((∑ j : Fin 3, (Ml j).comp (Rh j)) + (Ml i).comp Bh) u) := by
  have hterm (j : Fin 3) :
      I (Mh j (EG j u)) = Ml j (Rh j (MH u)) - ML (Ml j (Rh j u)) := by
    rw [c1, c3, map_add, c2]
    abel
  have hdeg : I (Mh i (HQ u)) = Ml i (Bh (MH u)) - ML (Ml i (Bh u)) := by
    rw [c1, c4, map_sub, c2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sum, hterm, hdeg, Finset.sum_sub_distrib]
  abel

/-- Lemma P2: `J E[Q,A] = MN A^l − A^l ML`. -/
theorem raising_multiplier_cancellation
    (J : Y →L[ℝ] Z) (Rl : Fin 3 → Y →L[ℝ] Z) (Bl : Y →L[ℝ] Z) (Ml : Fin 3 → Y →L[ℝ] Y)
    (ML : Y →L[ℝ] Y) (MN : Z →L[ℝ] Z) (EG : Fin 3 → Y →L[ℝ] Y) (HL : Y →L[ℝ] Y) (i : Fin 3)
    (d1 : ∀ j v, Ml j (ML v) = ML (Ml j v))
    (d2 : ∀ j v, Rl j (ML v) = MN (Rl j v) + J (EG j v))
    (d3 : ∀ v, J (HL v) = Bl (ML v) - MN (Bl v)) (v : Y) :
    J (((∑ j : Fin 3, (EG j).comp (Ml j)) - HL.comp (Ml i)) v) =
      MN (((-∑ j : Fin 3, (Rl j).comp (Ml j)) + Bl.comp (Ml i)) v) -
        ((-∑ j : Fin 3, (Rl j).comp (Ml j)) + Bl.comp (Ml i)) (ML v) := by
  have hterm (j : Fin 3) :
      Rl j (Ml j (ML v)) = MN (Rl j (Ml j v)) + J (EG j (Ml j v)) := by
    rw [d1, d2]
  have hdeg : Bl (Ml i (ML v)) = MN (Bl (Ml i v)) + J (HL (Ml i v)) := by
    rw [d1, d3]
    abel
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, map_neg, map_sum, hterm, hdeg, Finset.sum_add_distrib]
  abel

/-- Lemma P3: mixed lowering `C = CaT PH + Th E`. -/
theorem mixed_lowering_cancellation
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (CaT Th : X →L[ℝ] Y) (Tl : Y →L[ℝ] Z)
    (PH : X →L[ℝ] X) (PL : Y →L[ℝ] Y) (E : X →L[ℝ] X) (aH : X →L[ℝ] Y) (aL : Y →L[ℝ] Z)
    (e1 : ∀ x, J (CaT x) = aL (Th x) - Tl (aH x)) (e2 : ∀ x, J (Th x) = Tl (I x))
    (e3 : ∀ x, I (E x) = aH (PH x) - PL (aH x)) (u : X) :
    J ((CaT.comp PH + Th.comp E) u) = aL (Th (PH u)) - Tl (PL (aH u)) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, map_add]
  rw [e1, e2, e3, map_sub]
  abel

/-- Lemma P4: mixed raising `C = −PL CAS + E Sh`. -/
theorem mixed_raising_cancellation
    (J : Y →L[ℝ] Z) (CAS Sh : X →L[ℝ] Y) (Sl : Y →L[ℝ] Z) (PL : Y →L[ℝ] Y) (PN : Z →L[ℝ] Z)
    (E : Y →L[ℝ] Y) (AH : X →L[ℝ] Y) (AL : Y →L[ℝ] Z)
    (f1 : ∀ x, J (CAS x) = AL (Sh x) - Sl (AH x)) (f2 : ∀ v, J (PL v) = PN (J v))
    (f3 : ∀ v, J (E v) = PN (AL v) - AL (PL v)) (u : X) :
    J ((-(PL.comp CAS) + E.comp Sh) u) = PN (Sl (AH u)) - AL (PL (Sh u)) := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply, map_add, map_neg]
  rw [f2, f1, f3, map_sub]
  abel

end Generic

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualAngularPiDraft
