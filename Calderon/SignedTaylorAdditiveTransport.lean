import Calderon.SignedTaylorFixedLinearTransport

/-! Actual product curve and fixed projections. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma secondTaylorRemainder_add (F G : ℝ → V) (r : ℝ)
    (hF : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (θ*r))
    (hG : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ G (θ*r)) :
    secondTaylorRemainder (fun t => F t+G t) r =
      secondTaylorRemainder F r+secondTaylorRemainder G r := by
  let H := fun t : ℝ => (F t,G t)
  let P : V × V →L[ℝ] V := ContinuousLinearMap.fst ℝ V V
  let Q : V × V →L[ℝ] V := ContinuousLinearMap.snd ℝ V V
  have hH (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ H (θ*r) :=
    (hF θ hθ).prodMk (hG θ hθ)
  have hP : P (secondTaylorRemainder H r) = secondTaylorRemainder F r :=
    secondTaylorRemainder_fixed_linear_map H P r hH
  have hQ : Q (secondTaylorRemainder H r) = secondTaylorRemainder G r :=
    secondTaylorRemainder_fixed_linear_map H Q r hH
  have hSum : (P+Q) (secondTaylorRemainder H r) =
      secondTaylorRemainder (fun t => F t+G t) r :=
    secondTaylorRemainder_fixed_linear_map H (P+Q) r hH
  exact hSum.symm.trans (congrArg₂ (fun x y : V => x+y) hP hQ)

lemma secondTaylorRemainder_sub (F G : ℝ → V) (r : ℝ)
    (hF : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (θ*r))
    (hG : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ G (θ*r)) :
    secondTaylorRemainder (fun t => F t-G t) r =
      secondTaylorRemainder F r-secondTaylorRemainder G r := by
  let H := fun t : ℝ => (F t,G t)
  let P : V × V →L[ℝ] V := ContinuousLinearMap.fst ℝ V V
  let Q : V × V →L[ℝ] V := ContinuousLinearMap.snd ℝ V V
  have hH (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ ∞ H (θ*r) :=
    (hF θ hθ).prodMk (hG θ hθ)
  have hP : P (secondTaylorRemainder H r) = secondTaylorRemainder F r :=
    secondTaylorRemainder_fixed_linear_map H P r hH
  have hQ : Q (secondTaylorRemainder H r) = secondTaylorRemainder G r :=
    secondTaylorRemainder_fixed_linear_map H Q r hH
  have hSub : (P-Q) (secondTaylorRemainder H r) =
      secondTaylorRemainder (fun t => F t-G t) r :=
    secondTaylorRemainder_fixed_linear_map H (P-Q) r hH
  exact hSub.symm.trans (congrArg₂ (fun x y : V => x-y) hP hQ)

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_add
#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_sub
