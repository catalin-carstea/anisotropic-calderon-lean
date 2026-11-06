import Calderon.QuarticFourPairingIdentity
import Calderon.SphereSobolevQuarticPivotGraphs
import Calderon.SphereSobolevQuarticCommutatorForm
import Calderon.RealPivotDifferenceCancellation
import Calderon.SphereSobolevPairingInclusion

/-! Full upfront: day-oct13/full-quartic-form-author-oct15-v001/
PIVOT-IDENTITY-EXPANSION-v002.md. Conditional exact native endpoint/pivot graph
algebra. Actual finite high first-output representatives are not asserted. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic

lemma sphereSobolevHalfDualPairing_sub_left
    (a b : SphereSobolev (-(1/2 : ℝ))) (c : SphereSobolev (1/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ)) (a-b) c =
      sphereSobolevDualPairing (-(1/2 : ℝ)) a c -
        sphereSobolevDualPairing (-(1/2 : ℝ)) b c := by
  exact inner_sub_left a b c

attribute [local irreducible] sphereSobolevInclusionL sphereSobolevQuarticCommutatorWeakForm
  sphereSobolevDualPairing

theorem sphereSobolevQuarticWeakForm_eq_square_difference_of_pivot_graphs
    (SHigh SdagHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (SLow SdagLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (CLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (hS : ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (SHigh v) =
        SLow (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v))
    (hT : ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (SdagHigh v) =
        SdagLow (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v))
    (hC : ∀ v : SphereSobolev (3/2 : ℝ),
      CLow (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) =
        sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CHigh v))
    (hBracket : ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CHigh v) =
        SdagLow (SHigh v) - SLow (SdagHigh v))
    (hSAdj : ∀ z : SphereSobolev (1/2 : ℝ), ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevDualPairing (-(1/2 : ℝ)) (SLow z)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) =
      ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) z,
        sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (SdagHigh v)⟫_ℝ)
    (hTAdj : ∀ z : SphereSobolev (1/2 : ℝ), ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevDualPairing (-(1/2 : ℝ)) (SdagLow z)
        (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) =
      ⟪sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) z,
        sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (SHigh v)⟫_ℝ)
    (u su tu : SphereSobolev (3/2 : ℝ))
    (hsu : sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) su = SHigh u)
    (htu : sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) tu = SdagHigh u) :
    sphereSobolevQuarticCommutatorWeakForm SHigh SdagHigh SLow SdagLow CHigh CLow u =
      ‖sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (SHigh su)‖^2 -
        ‖sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (SdagHigh tu)‖^2 := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  have hCu : CHigh u = SdagHigh su - SHigh tu := by
    exact sphereSobolevQuarticHighBracket_eq_on_first_output_representatives
      SHigh SdagHigh SLow SdagLow CHigh hS hT hBracket u su tu hsu htu
  have hOuter (v : SphereSobolev (3/2 : ℝ)) :
      sphereSobolevDualPairing (-(1/2 : ℝ)) (CLow (I v)) (I v) =
        ‖Z (SHigh v)‖^2 - ‖Z (SdagHigh v)‖^2 := by
    exact sphereSobolevQuarticBracketQuadraticPairing_eq_square_difference
      SHigh SdagHigh SLow SdagLow CHigh CLow hC hBracket hSAdj hTAdj v
  let P : SphereSobolev (-(1/2 : ℝ)) → SphereSobolev (1/2 : ℝ) → ℝ :=
    fun a b => sphereSobolevDualPairing (-(1/2 : ℝ)) a b
  have hAlgebra : P (CLow (SHigh u)) (SHigh u) + P (SLow (CHigh u)) (SHigh u) +
      P (SdagLow (CHigh u)) (SdagHigh u) + P (CLow (SdagHigh u)) (SdagHigh u) =
        ‖Z (SHigh su)‖^2 - ‖Z (SdagHigh tu)‖^2 :=
    quartic_four_pairing_eq_square_difference
      (U := SphereSobolev (3/2 : ℝ)) (V := SphereSobolev (1/2 : ℝ))
      (W := SphereSobolev (-(1/2 : ℝ))) (H := SphereSobolev 0)
      I Z.toLinearMap P SHigh SdagHigh CHigh SLow SdagLow CLow
      hOuter hSAdj hTAdj u su tu hsu htu hCu
  unfold sphereSobolevQuarticCommutatorWeakForm
  exact hAlgebra

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevHalfDualPairing_sub_left
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevQuarticWeakForm_eq_square_difference_of_pivot_graphs
