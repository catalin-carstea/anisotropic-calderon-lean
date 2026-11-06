import Calderon.RealPivotDifferenceCancellation
import Calderon.SphereSobolevPairingInclusion

/-! The intermediate graphs of the native pivots. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
attribute [local irreducible] sphereSobolevInclusionL

lemma sphereSobolevQuarticHighBracket_eq_on_first_output_representatives
    (SHigh SdagHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (SLow SdagLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (hS : ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (SHigh v) =
        SLow (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v))
    (hT : ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (SdagHigh v) =
        SdagLow (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v))
    (hBracket : ∀ v : SphereSobolev (3/2 : ℝ),
      sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (CHigh v) =
        SdagLow (SHigh v) - SLow (SdagHigh v))
    (u su tu : SphereSobolev (3/2 : ℝ))
    (hsu : sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) su = SHigh u)
    (htu : sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) tu = SdagHigh u) :
    CHigh u = SdagHigh su - SHigh tu := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  have hJInjective : Function.Injective J :=
    sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hTS : J (SdagHigh su) = SdagLow (SHigh u) :=
    (hT su).trans (congrArg SdagLow hsu)
  have hST : J (SHigh tu) = SLow (SdagHigh u) :=
    (hS tu).trans (congrArg SLow htu)
  have hPair : SdagLow (SHigh u) - SLow (SdagHigh u) =
      J (SdagHigh su) - J (SHigh tu) :=
    congrArg₂ (fun a b : SphereSobolev (-(1/2 : ℝ)) => a-b) hTS.symm hST.symm
  have hCuJ : J (CHigh u) = J (SdagHigh su - SHigh tu) :=
    (hBracket u).trans (hPair.trans (J.map_sub _ _).symm)
  exact hJInjective hCuJ

lemma sphereSobolevQuarticBracketQuadraticPairing_eq_square_difference
    (SHigh SdagHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (SLow SdagLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
    (CHigh : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
    (CLow : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)))
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
    (v : SphereSobolev (3/2 : ℝ)) :
    sphereSobolevDualPairing (-(1/2 : ℝ))
      (CLow (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v))
      (sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num) v) =
    ‖sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (SHigh v)‖^2 -
      ‖sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num) (SdagHigh v)‖^2 := by
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (-(1/2 : ℝ)) :=
    sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  let Z : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  have hCv : CLow (I v) = SdagLow (SHigh v) - SLow (SdagHigh v) :=
    (hC v).trans (hBracket v)
  have hPair := congrArg
    (fun z : SphereSobolev (-(1/2 : ℝ)) => sphereSobolevDualPairing (-(1/2 : ℝ)) z (I v)) hCv
  have hSplit : sphereSobolevDualPairing (-(1/2 : ℝ))
      (SdagLow (SHigh v) - SLow (SdagHigh v)) (I v) =
      sphereSobolevDualPairing (-(1/2 : ℝ)) (SdagLow (SHigh v)) (I v) -
        sphereSobolevDualPairing (-(1/2 : ℝ)) (SLow (SdagHigh v)) (I v) :=
    inner_sub_left (𝕜 := ℝ) (SdagLow (SHigh v)) (SLow (SdagHigh v)) (I v)
  have hAdj := congrArg₂ (fun a b : ℝ => a-b) (hTAdj (SHigh v) v) (hSAdj (SdagHigh v) v)
  have hNorm : ⟪Z (SHigh v),Z (SHigh v)⟫_ℝ -
      ⟪Z (SdagHigh v),Z (SdagHigh v)⟫_ℝ = ‖Z (SHigh v)‖^2 - ‖Z (SdagHigh v)‖^2 :=
    congrArg₂ (fun a b : ℝ => a-b)
      (real_inner_self_eq_norm_sq (F := SphereSobolev 0) (Z (SHigh v)))
      (real_inner_self_eq_norm_sq (F := SphereSobolev 0) (Z (SdagHigh v)))
  exact hPair.trans (hSplit.trans (hAdj.trans hNorm))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevQuarticHighBracket_eq_on_first_output_representatives
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevQuarticBracketQuadraticPairing_eq_square_difference
