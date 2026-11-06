import Calderon.ConnectionErrorSuffix
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI.AnisotropicCalderon.ConnectionError
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def koszulFunctional (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) : E →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ E (D X Y) + InnerProductSpace.toDual ℝ E (D Y X) -
    (InnerProductSpace.toDual ℝ E Y).comp (D.flip X)

lemma koszulFunctional_apply (D : E →L[ℝ] E →L[ℝ] E) (X Y Z : E) :
    koszulFunctional D X Y Z = inner ℝ (D X Y) Z + inner ℝ (D Y X) Z -
      inner ℝ (D Z X) Y := by
  simp [koszulFunctional, real_inner_comm]

noncomputable def coordinateConnection (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (X Y : E) : E :=
  (1/2 : ℝ) • Q ((InnerProductSpace.toDual ℝ E).symm (koszulFunctional D X Y))

theorem coordinateConnection_koszul (Q M : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hMQ : ∀ z, M (Q z) = z) (X Y Z : E) :
    2 * inner ℝ (M (coordinateConnection Q D X Y)) Z =
      inner ℝ (D X Y) Z + inner ℝ (D Y X) Z - inner ℝ (D Z X) Y := by
  simp only [coordinateConnection, map_smul, hMQ, real_inner_smul_left,
    InnerProductSpace.toDual_symm_apply]
  rw [koszulFunctional_apply]
  ring

theorem coordinateConnection_symmetric (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E)
    (hD : ∀ U X Y, inner ℝ (D U X) Y = inner ℝ (D U Y) X) (X Y : E) :
    coordinateConnection Q D X Y = coordinateConnection Q D Y X := by
  have hf : koszulFunctional D X Y = koszulFunctional D Y X := by
    ext Z
    simp only [koszulFunctional_apply]
    rw [hD Z X Y]
    ring
  simp only [coordinateConnection, hf]

theorem inverse_metric_derivative_symmetric
    (M : E → E →L[ℝ] E) (DM : E →L[ℝ] E →L[ℝ] E) (x : E)
    (hM : HasFDerivAt M DM x)
    (hsym : ∀ᶠ y in 𝓝 x, ∀ X Z, inner ℝ (M y X) Z = inner ℝ (M y Z) X)
    (U X Z : E) : inner ℝ (DM U X) Z = inner ℝ (DM U Z) X := by
  have hX := hM.clm_apply (hasFDerivAt_const X x)
  have hZ := hM.clm_apply (hasFDerivAt_const Z x)
  have h₁ := (InnerProductSpace.toDual ℝ E Z).hasFDerivAt.comp x hX
  have h₂ := (InnerProductSpace.toDual ℝ E X).hasFDerivAt.comp x hZ
  have heq : (fun y => InnerProductSpace.toDual ℝ E Z (M y X)) =ᶠ[𝓝 x]
      (fun y => InnerProductSpace.toDual ℝ E X (M y Z)) := by
    filter_upwards [hsym] with y hy
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hy X Z
  have hd := (h₁.congr_of_eventuallyEq heq.symm).unique h₂
  have hv := congrArg (fun L => L U) hd
  have hs : inner ℝ Z (DM U X) = inner ℝ X (DM U Z) := by simpa using hv
  calc
    inner ℝ (DM U X) Z = inner ℝ Z (DM U X) := real_inner_comm _ _
    _ = inner ℝ X (DM U Z) := hs
    _ = inner ℝ (DM U Z) X := real_inner_comm _ _

theorem norm_coordinateConnection_le
    (Q M : E →L[ℝ] E) (DQ DM : E →L[ℝ] E →L[ℝ] E)
    (κ d : ℝ) (hκ : κ ≤ 1/4) (hd : 0 ≤ d)
    (hQ : ∀ z, ‖Q z-z‖ ≤ κ*‖z‖)
    (hQM : ∀ z, Q (M z)=z) (hMQ : ∀ z, M (Q z)=z)
    (hDQ : ∀ X Z, ‖DQ X Z‖ ≤ d*‖X‖*‖Z‖)
    (hDM : ∀ X Z, DM X Z = -M (DQ X (M Z))) (X Y : E) :
    ‖coordinateConnection Q DM X Y‖ ≤ (10/3)*d*‖X‖*‖Y‖ :=
  norm_connection_le Q M DQ DM (coordinateConnection Q DM) κ d hκ hd hQ hQM
    hDQ hDM (coordinateConnection_koszul Q M DM hMQ) X Y

theorem norm_coordinateConnection_at_le
    (Q M : E → E →L[ℝ] E) (DQ DM : E →L[ℝ] E →L[ℝ] E)
    (x : E) (κ d : ℝ) (hκ : κ ≤ 1/4) (hd : 0 ≤ d)
    (hQd : HasFDerivAt Q DQ x) (hMd : HasFDerivAt M DM x)
    (hQ : ∀ z, ‖Q x z-z‖ ≤ κ*‖z‖)
    (hQM : (fun y => (Q y).comp (M y)) =ᶠ[𝓝 x]
      fun _ => ContinuousLinearMap.id ℝ E)
    (hMQ : ∀ z, M x (Q x z)=z)
    (hDQ : ∀ X Z, ‖DQ X Z‖ ≤ d*‖X‖*‖Z‖) (X Y : E) :
    ‖coordinateConnection (Q x) DM X Y‖ ≤ (10/3)*d*‖X‖*‖Y‖ := by
  have hQMx : ∀ z, Q x (M x z)=z := by
    intro z
    have h := hQM.self_of_nhds
    simpa using congrArg (fun L => L z) h
  exact norm_coordinateConnection_le (Q x) (M x) DQ DM κ d hκ hd hQ hQMx hMQ
    hDQ (inverse_derivative_apply Q M DQ DM x hQd hMd hQM hMQ) X Y

#print axioms coordinateConnection_koszul
#print axioms inverse_metric_derivative_symmetric
#print axioms norm_coordinateConnection_le
#print axioms norm_coordinateConnection_at_le
end OAI.AnisotropicCalderon.ConnectionError
