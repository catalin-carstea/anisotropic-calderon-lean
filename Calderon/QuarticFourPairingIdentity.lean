import Calderon.RealPivotDifferenceCancellation
import Mathlib.Tactic.Linarith
/-! Pure real pairing algebra. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma quartic_four_pairing_eq_square_difference
    {U V W H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (I : U → V) (Z : V →ₗ[ℝ] H) (P : W → V → ℝ)
    (S T C : U → V) (s t c : V → W)
    (hOuter : ∀ v : U, P (c (I v)) (I v) = ‖Z (S v)‖^2 - ‖Z (T v)‖^2)
    (hSAdj : ∀ z : V, ∀ v : U, P (s z) (I v) = ⟪Z z,Z (T v)⟫_ℝ)
    (hTAdj : ∀ z : V, ∀ v : U, P (t z) (I v) = ⟪Z z,Z (S v)⟫_ℝ)
    (u su tu : U) (hsu : I su = S u) (htu : I tu = T u)
    (hCu : C u = T su - S tu) :
    P (c (S u)) (S u) + P (s (C u)) (S u) +
      P (t (C u)) (T u) + P (c (T u)) (T u) =
        ‖Z (S su)‖^2 - ‖Z (T tu)‖^2 := by
  have hFirst : P (c (S u)) (S u) = ‖Z (S su)‖^2 - ‖Z (T su)‖^2 :=
    (congrArg (fun z : V => P (c z) z) hsu.symm).trans (hOuter su)
  have hFourth : P (c (T u)) (T u) = ‖Z (S tu)‖^2 - ‖Z (T tu)‖^2 :=
    (congrArg (fun z : V => P (c z) z) htu.symm).trans (hOuter tu)
  have hSecond : P (s (C u)) (S u) = ⟪Z (C u),Z (T su)⟫_ℝ :=
    (congrArg (fun z : V => P (s (C u)) z) hsu.symm).trans (hSAdj (C u) su)
  have hThird : P (t (C u)) (T u) = ⟪Z (C u),Z (S tu)⟫_ℝ :=
    (congrArg (fun z : V => P (t (C u)) z) htu.symm).trans (hTAdj (C u) tu)
  have hZCu : Z (C u) = Z (T su) - Z (S tu) :=
    (congrArg Z hCu).trans (Z.map_sub _ _)
  have hMiddle : ⟪Z (C u),Z (T su)⟫_ℝ + ⟪Z (C u),Z (S tu)⟫_ℝ =
      ‖Z (T su)‖^2 - ‖Z (S tu)‖^2 := by
    rw [hZCu]
    exact real_inner_difference_sum_eq_norm_sq_sub (Z (T su)) (Z (S tu))
  rw [hFirst,hSecond,hThird,hFourth]
  linarith

end OAI.AnisotropicCalderon.SphereHarmonic
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.quartic_four_pairing_eq_square_difference
