import Calderon.SignedTaylorFixedLinearTransport

/-! Exact fixed-inclusion integral transport on abstract normed spaces; the actual
native graphs are treated separately. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError

lemma secondTaylorRemainder_operator_intertwining
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (F : ℝ → X →L[ℝ] Y) (A : ℝ → Y →L[ℝ] Z)
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (r : ℝ)
    (hF : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ F (θ*r))
    (hA : ∀ θ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ A (θ*r))
    (hEq : ∀ θ ∈ Icc (0 : ℝ) 1,
      (fun z => J.comp (F z)) =ᶠ[𝓝 (θ*r)] (fun z => (A z).comp I)) :
    J.comp (secondTaylorRemainder F r) = (secondTaylorRemainder A r).comp I := by
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
  have hPostApply (T : X →L[ℝ] Y) : Post T = J.comp T := rfl
  have hPreApply (T : Y →L[ℝ] Z) : Pre T = T.comp I := rfl
  have hSame (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) :
      (fun z => Post (F z)) =ᶠ[𝓝 (θ*r)] (fun z => Pre (A z)) := by
    filter_upwards [hEq θ hθ] with z hz
    exact (hPostApply _).trans (hz.trans (hPreApply _).symm)
  have hFmap : Post (secondTaylorRemainder F r) =
      secondTaylorRemainder (fun z => Post (F z)) r :=
    secondTaylorRemainder_fixed_linear_map F Post r hF
  have hAmap : Pre (secondTaylorRemainder A r) =
      secondTaylorRemainder (fun z => Pre (A z)) r :=
    secondTaylorRemainder_fixed_linear_map A Pre r hA
  have hMiddle : secondTaylorRemainder (fun z => Post (F z)) r =
      secondTaylorRemainder (fun z => Pre (A z)) r :=
    secondTaylorRemainder_eq_of_locallyEq_on_segment _ _ r hSame
  exact (hPostApply _).symm.trans
    (hFmap.trans (hMiddle.trans (hAmap.symm.trans (hPreApply _))))

end OAI.AnisotropicCalderon.ConnectionError
#print axioms OAI.AnisotropicCalderon.ConnectionError.secondTaylorRemainder_operator_intertwining
