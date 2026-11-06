import Calderon.ActualFullEPhysicalEndpoints

/-! Full-Half gained pivot by two dense-inclusion extensions.
Root auxiliary proof; complete before-code statement in cubic-low-pivot-upfront-v001.
No actual endpoint producer, final bound or semantic acceptance is asserted. -/
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCubicLowPivot
variable {E H N ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

/-- A produced paired upper graph gives the genuine pivot on all Half inputs. -/
theorem paired_low_pivot_of_dense_inclusion
    (I : E →L[ℝ] H) (J : H →L[ℝ] N) (P : H →L[ℝ] N →L[ℝ] ℝ)
    (G : ι → ι → E →L[ℝ] H) (Cl : ι → ι → H →L[ℝ] N)
    (hDense : DenseRange I)
    (hUpper : ∀ a b u, Cl a b (I u)=J (G a b u))
    (hPaired : ∀ a b u v, P (I v) (J (G a b u))=P (I u) (J (G b a v)))
    (a b : ι) (x y : H) : P x (Cl a b y)=P y (Cl b a x) := by
  have hRange (u v : E) : P (I u) (Cl a b (I v))=P (I v) (Cl b a (I u)) := by
    rw [hUpper a b v,hUpper b a u]
    exact hPaired a b v u
  have hFirst (v : E) (z : H) : P z (Cl a b (I v))=P (I v) (Cl b a z) := by
    refine hDense.induction_on z
      (isClosed_eq (P.continuous.clm_apply continuous_const)
        ((P (I v)).continuous.comp (Cl b a).continuous)) ?_
    intro u
    exact hRange u v
  refine hDense.induction_on y
    (isClosed_eq ((P x).continuous.comp (Cl a b).continuous)
      (P.continuous.clm_apply continuous_const)) ?_
  intro v
  exact hFirst v x
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCubicLowPivot
