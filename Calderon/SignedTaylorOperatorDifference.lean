import Calderon.SignedTaylorOperatorIntertwining
import Calderon.SignedTaylorAdditiveTransport

/-! Fixed composition difference; no intertwining is assumed. -/
set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.ConnectionError

lemma secondTaylorRemainder_operator_difference
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (F : ℝ → X →L[ℝ] Y) (A : ℝ → Y →L[ℝ] Z)
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (r : ℝ)
    (hF : ∀ θ ∈ Icc (0:ℝ) 1, ContDiffAt ℝ ∞ F (θ*r))
    (hA : ∀ θ ∈ Icc (0:ℝ) 1, ContDiffAt ℝ ∞ A (θ*r)) :
    secondTaylorRemainder (fun z => J.comp (F z)-(A z).comp I) r =
      J.comp (secondTaylorRemainder F r)-(secondTaylorRemainder A r).comp I := by
  let postLinear : (X →L[ℝ] Y) →ₗ[ℝ] (X →L[ℝ] Z) :=
    { toFun := fun T => J.comp T
      map_add' := fun T U => by
        apply ContinuousLinearMap.ext
        intro x
        exact J.map_add (T x) (U x)
      map_smul' := fun c T => by
        apply ContinuousLinearMap.ext
        intro x
        exact J.map_smul c (T x) }
  let Post : (X →L[ℝ] Y) →L[ℝ] (X →L[ℝ] Z) :=
    LinearMap.mkContinuous postLinear ‖J‖ (fun T => J.opNorm_comp_le T)
  let preLinear : (Y →L[ℝ] Z) →ₗ[ℝ] (X →L[ℝ] Z) :=
    { toFun := fun T => T.comp I
      map_add' := fun T U => rfl
      map_smul' := fun c T => rfl }
  have hPreBound (T : Y →L[ℝ] Z) : ‖preLinear T‖ ≤ ‖I‖*‖T‖ :=
    (T.opNorm_comp_le I).trans_eq (mul_comm _ _)
  let Pre : (Y →L[ℝ] Z) →L[ℝ] (X →L[ℝ] Z) :=
    LinearMap.mkContinuous preLinear ‖I‖ hPreBound
  have hPostApply (T : X →L[ℝ] Y) : Post T=J.comp T := rfl
  have hPreApply (T : Y →L[ℝ] Z) : Pre T=T.comp I := rfl
  have hPostSmooth (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) :
      ContDiffAt ℝ ∞ (fun z => Post (F z)) (θ*r) :=
    Post.contDiff.contDiffAt.comp (θ*r) (hF θ hθ)
  have hPreSmooth (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) :
      ContDiffAt ℝ ∞ (fun z => Pre (A z)) (θ*r) :=
    Pre.contDiff.contDiffAt.comp (θ*r) (hA θ hθ)
  have hSub := secondTaylorRemainder_sub (fun z => Post (F z)) (fun z => Pre (A z)) r
    hPostSmooth hPreSmooth
  have hPost : secondTaylorRemainder (fun z => Post (F z)) r = J.comp (secondTaylorRemainder F r) :=
    (secondTaylorRemainder_fixed_linear_map F Post r hF).symm.trans (hPostApply _)
  have hPre : secondTaylorRemainder (fun z => Pre (A z)) r = (secondTaylorRemainder A r).comp I :=
    (secondTaylorRemainder_fixed_linear_map A Pre r hA).symm.trans (hPreApply _)
  simpa only [hPostApply,hPreApply] using
    hSub.trans (congrArg₂ (fun U V : X →L[ℝ] Z => U-V) hPost hPre)

end OAI.AnisotropicCalderon.ConnectionError
#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_operator_difference
