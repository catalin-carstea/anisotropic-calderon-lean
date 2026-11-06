import TauCeti.Analysis.InnerProductSpace.LaxMilgram

/-! EXPANSION.json precedes the literal source-functional strict-minimum derivation. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.ExteriorSource
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def coerciveSourceFunctional (A : V →L[ℝ] V →L[ℝ] ℝ) (F : StrongDual ℝ V) (v : V) : ℝ :=
  (1/2 : ℝ) * A v v - F v

lemma coerciveSourceFunctional_gap (A : V →L[ℝ] V →L[ℝ] ℝ) (F : StrongDual ℝ V)
    (hSym : ∀ v w : V, A v w = A w v) (u : V)
    (hSolve : ∀ v : V, A u v = F v) (v : V) :
    coerciveSourceFunctional A F v - coerciveSourceFunctional A F u =
      (1/2 : ℝ) * A (v-u) (v-u) := by
  simp only [coerciveSourceFunctional, map_sub, ContinuousLinearMap.sub_apply]
  rw [hSym v u,hSolve v,hSolve u]
  ring

lemma coerciveSourceFunctional_min (A : V →L[ℝ] V →L[ℝ] ℝ) (F : StrongDual ℝ V)
    (hCo : IsCoercive A) (hSym : ∀ v w : V, A v w = A w v) (u : V)
    (hSolve : ∀ v : V, A u v = F v) (v : V) :
    coerciveSourceFunctional A F u ≤ coerciveSourceFunctional A F v := by
  have hGap := coerciveSourceFunctional_gap A F hSym u hSolve v
  have hDiag := hCo.apply_self_nonneg (v-u)
  linarith

lemma eq_of_coerciveSourceFunctional_eq_min (A : V →L[ℝ] V →L[ℝ] ℝ) (F : StrongDual ℝ V)
    (hCo : IsCoercive A) (hSym : ∀ v w : V, A v w = A w v) (u : V)
    (hSolve : ∀ v : V, A u v = F v) (v : V)
    (hEqual : coerciveSourceFunctional A F v = coerciveSourceFunctional A F u) : v = u := by
  have hGap := coerciveSourceFunctional_gap A F hSym u hSolve v
  have hZero : A (v-u) (v-u) = 0 := by
    rw [hEqual,sub_self] at hGap
    linarith
  rcases hCo with ⟨c,hc,hBound⟩
  have hLe : c * (‖v-u‖ * ‖v-u‖) ≤ 0 := by
    simpa only [mul_assoc,hZero] using hBound (v-u)
  have hSquareLe : ‖v-u‖ * ‖v-u‖ ≤ 0 :=
    (mul_le_mul_iff_left₀ hc).mp (by
      calc
        (‖v-u‖ * ‖v-u‖) * c = c * (‖v-u‖ * ‖v-u‖) := mul_comm _ _
        _ ≤ 0 := hLe
        _ = 0 * c := (zero_mul c).symm)
  have hSquare : ‖v-u‖ * ‖v-u‖ = 0 :=
    le_antisymm hSquareLe (mul_self_nonneg _)
  have hDiff : v-u = 0 := norm_eq_zero.mp (mul_self_eq_zero.mp hSquare)
  exact sub_eq_zero.mp hDiff

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.coerciveSourceFunctional
#print axioms OAI.AnisotropicCalderon.ExteriorSource.coerciveSourceFunctional_gap
#print axioms OAI.AnisotropicCalderon.ExteriorSource.coerciveSourceFunctional_min
#print axioms OAI.AnisotropicCalderon.ExteriorSource.eq_of_coerciveSourceFunctional_eq_min
