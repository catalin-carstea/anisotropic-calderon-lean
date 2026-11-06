import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

noncomputable section
open InnerProductSpace ContinuousLinearMap
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily

variable {V E F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual inverse of a coercive form, written without a parameter-dependent proof. -/
def functionalInverse (B : V →L[ℝ] V →L[ℝ] ℝ) : StrongDual ℝ V →L[ℝ] V :=
  (continuousLinearMapOfBilin B).inverse.comp
    (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem functionalInverse_apply (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : StrongDual ℝ V) :
    functionalInverse B ell = hB.solutionOfFunctional ell := by
  change (continuousLinearMapOfBilin B).inverse
    ((InnerProductSpace.toDual ℝ V).symm ell) = _
  have he : (hB.continuousLinearEquivOfBilin : V →L[ℝ] V) =
      continuousLinearMapOfBilin B := rfl
  rw [← he, inverse_equiv]
  rfl

theorem apply_functionalInverse (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : StrongDual ℝ V) (v : V) :
    B (functionalInverse B ell) v = ell v := by
  rw [functionalInverse_apply B hB]
  exact hB.apply_solutionOfFunctional_eq ell v

theorem eq_functionalInverse (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (ell : StrongDual ℝ V) (u : V)
    (hu : ∀ v, B u v = ell v) : u = functionalInverse B ell := by
  rw [functionalInverse_apply B hB]
  exact hB.eq_solutionOfFunctional hu

theorem norm_functionalInverse_apply_le (B : V →L[ℝ] V →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hB : ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u)
    (ell : StrongDual ℝ V) : ‖functionalInverse B ell‖ ≤ C⁻¹ * ‖ell‖ := by
  let u := functionalInverse B ell
  have hc : IsCoercive B := ⟨C, hC, hB⟩
  have hbound : C * ‖u‖ * ‖u‖ ≤ ‖ell‖ * ‖u‖ := calc
    C * ‖u‖ * ‖u‖ ≤ B u u := hB u
    _ = ell u := apply_functionalInverse B hc ell u
    _ ≤ ‖ell u‖ := le_abs_self _
    _ ≤ ‖ell‖ * ‖u‖ := ell.le_opNorm u
  by_cases hu : u = 0
  · simp [u, hu, mul_nonneg (inv_nonneg.mpr hC.le) (norm_nonneg ell)]
  · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcancel : C * ‖u‖ ≤ ‖ell‖ := (mul_le_mul_iff_left₀ hn).mp hbound
    change ‖u‖ ≤ C⁻¹ * ‖ell‖
    exact (le_inv_mul_iff₀ hC).2 hcancel

theorem norm_functionalInverse_le (B : V →L[ℝ] V →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 < C) (hB : ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u) :
    ‖functionalInverse B‖ ≤ C⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hC.le)
  exact norm_functionalInverse_apply_le B C hC hB

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem uniform_norm_functionalInverse_le (B : E → V →L[ℝ] V →L[ℝ] ℝ)
    (s : Set E) (C : ℝ) (hC : 0 < C)
    (hB : ∀ x ∈ s, ∀ u, C * ‖u‖ * ‖u‖ ≤ B x u u) :
    ∀ x ∈ s, ‖functionalInverse (B x)‖ ≤ C⁻¹ := by
  intro x hx
  exact norm_functionalInverse_le (B x) C hC (hB x hx)

theorem contDiffOn_functionalInverse {n : WithTop ℕ∞}
    (B : E → V →L[ℝ] V →L[ℝ] ℝ) (s : Set E)
    (hB : ContDiffOn ℝ n B s) (hc : ∀ x ∈ s, IsCoercive (B x)) :
    ContDiffOn ℝ n (fun x => functionalInverse (B x)) s := by
  have hA : ContDiffOn ℝ n (fun x => continuousLinearMapOfBilin (B x)) s :=
    contDiffOn_const.clm_comp hB
  have hI : ContDiffOn ℝ n
      (fun x => (continuousLinearMapOfBilin (B x)).inverse) s := by
    intro x hx
    have he : ((hc x hx).continuousLinearEquivOfBilin : V →L[ℝ] V) =
        continuousLinearMapOfBilin (B x) := rfl
    have hi := contDiffAt_map_inverse (n := n) (hc x hx).continuousLinearEquivOfBilin
    rw [he] at hi
    exact hi.comp_contDiffWithinAt x (hA x hx)
  exact hI.clm_comp contDiffOn_const

theorem contDiffOn_weightedSolution {n : WithTop ℕ∞}
    (B : E → V →L[ℝ] V →L[ℝ] ℝ) (M : E → F →L[ℝ] StrongDual ℝ V)
    (s : Set E) (hB : ContDiffOn ℝ n B s)
    (hc : ∀ x ∈ s, IsCoercive (B x)) (hM : ContDiffOn ℝ n M s) :
    ContDiffOn ℝ n (fun x => (functionalInverse (B x)).comp (M x)) s :=
  (contDiffOn_functionalInverse B s hB hc).clm_comp hM

end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.functionalInverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.functionalInverse_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.apply_functionalInverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.eq_functionalInverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.norm_functionalInverse_apply_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.norm_functionalInverse_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.uniform_norm_functionalInverse_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.contDiffOn_functionalInverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.contDiffOn_weightedSolution
