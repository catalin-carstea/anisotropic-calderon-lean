import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Full before-source: actual-covariant-leading-algebra-author-oct16-v001/
EXPANSION-polymorphic-product-iterated-derivative-bounds-v055.md. -/
set_option autoImplicit false
noncomputable section
open scoped ContDiff
universe u v w
namespace OAI.AnisotropicCalderon.ProductIteratedFDerivBounds

variable {D : Type u} {E : Type v} {F : Type w}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_fst_le
    {f : D → E × F} {x : D} {n : ℕ∞ω} {order : ℕ}
    (hf : ContDiffAt ℝ n f x) (horder : order ≤ n) :
    ‖iteratedFDeriv ℝ order (fun y => (f y).1) x‖ ≤
      ‖iteratedFDeriv ℝ order f x‖ := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PRODUCT_DERIVATIVE FIRST_ENTER"
    out.flush
  have hDerivative :
      iteratedFDeriv ℝ order (fun y => (f y).1) x =
        (ContinuousLinearMap.fst ℝ E F).compContinuousMultilinearMap
          (iteratedFDeriv ℝ order f x) :=
    (ContinuousLinearMap.fst ℝ E F).iteratedFDeriv_comp_left hf horder
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PRODUCT_DERIVATIVE FIRST_IDENTITY_READY"
    out.flush
  calc
    _ = ‖(ContinuousLinearMap.fst ℝ E F).compContinuousMultilinearMap
        (iteratedFDeriv ℝ order f x)‖ := congrArg norm hDerivative
    _ ≤ ‖iteratedFDeriv ℝ order f x‖ := by
      apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
      intro v
      change ‖((iteratedFDeriv ℝ order f x) v).1‖ ≤
        ‖iteratedFDeriv ℝ order f x‖ * ∏ i, ‖v i‖
      exact (norm_fst_le _).trans ((iteratedFDeriv ℝ order f x).le_opNorm v)

theorem norm_iteratedFDeriv_snd_le
    {f : D → E × F} {x : D} {n : ℕ∞ω} {order : ℕ}
    (hf : ContDiffAt ℝ n f x) (horder : order ≤ n) :
    ‖iteratedFDeriv ℝ order (fun y => (f y).2) x‖ ≤
      ‖iteratedFDeriv ℝ order f x‖ := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PRODUCT_DERIVATIVE SECOND_ENTER"
    out.flush
  have hDerivative :
      iteratedFDeriv ℝ order (fun y => (f y).2) x =
        (ContinuousLinearMap.snd ℝ E F).compContinuousMultilinearMap
          (iteratedFDeriv ℝ order f x) :=
    (ContinuousLinearMap.snd ℝ E F).iteratedFDeriv_comp_left hf horder
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "PRODUCT_DERIVATIVE SECOND_IDENTITY_READY"
    out.flush
  calc
    _ = ‖(ContinuousLinearMap.snd ℝ E F).compContinuousMultilinearMap
        (iteratedFDeriv ℝ order f x)‖ := congrArg norm hDerivative
    _ ≤ ‖iteratedFDeriv ℝ order f x‖ := by
      apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
      intro v
      change ‖((iteratedFDeriv ℝ order f x) v).2‖ ≤
        ‖iteratedFDeriv ℝ order f x‖ * ∏ i, ‖v i‖
      exact (norm_snd_le _).trans ((iteratedFDeriv ℝ order f x).le_opNorm v)

end OAI.AnisotropicCalderon.ProductIteratedFDerivBounds
