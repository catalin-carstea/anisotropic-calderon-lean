import Calderon.ParametricCoerciveInverse
import Calderon.SmoothSobolevBridge

set_option maxSynthPendingDepth 10
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

section General
variable {X J V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup J] [NormedSpace ℝ J]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- Tau's actual integrated L-infinity coefficient form, bundled linearly in its coefficient. -/
def lpBilinearFormL (mu : Measure X) :
    Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ mu →L[ℝ]
      Lp J 2 mu →L[ℝ] Lp J 2 mu →L[ℝ] ℝ :=
  let pairing := (ContinuousLinearMap.apply ℝ ℝ (E := J)).flip.lpPairing mu 2 2
  let holder := (ContinuousLinearMap.apply ℝ (J →L[ℝ] ℝ) (E := J)).flip.holderL
    mu ⊤ 2 2
  (ContinuousLinearMap.compL ℝ (Lp J 2 mu) (Lp (J →L[ℝ] ℝ) 2 mu)
    (Lp J 2 mu →L[ℝ] ℝ) pairing).comp holder

theorem lpBilinearFormL_apply (mu : Measure X)
    (C : Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ mu) :
    lpBilinearFormL mu C = TauCeti.lpBilinearForm mu C := rfl

/-- Restrict both arguments along the same fixed inclusion, preserving the actual form. -/
def restrictBilinearL (i : V →L[ℝ] J) :
    (J →L[ℝ] J →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ :=
  let first := (ContinuousLinearMap.compL ℝ V J (J →L[ℝ] ℝ)).flip i
  let flipFirst := (ContinuousLinearMap.flipₗᵢ ℝ V J ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let second := (ContinuousLinearMap.compL ℝ V J (V →L[ℝ] ℝ)).flip i
  let flipSecond := (ContinuousLinearMap.flipₗᵢ ℝ V V ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  flipSecond.comp (second.comp (flipFirst.comp first))

theorem restrictBilinearL_apply (i : V →L[ℝ] J) (B : J →L[ℝ] J →L[ℝ] ℝ) :
    restrictBilinearL i B = B.bilinearComp i i := rfl
/-- Construct the coefficient map before specializing the Sobolev carrier. -/
def coefficientFormL (mu : Measure X) (i : V →L[ℝ] Lp J 2 mu) :
    Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ mu →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ :=
  (restrictBilinearL i).comp (lpBilinearFormL mu)

theorem coefficientFormL_apply (mu : Measure X) (i : V →L[ℝ] Lp J 2 mu)
    (C : Lp (J →L[ℝ] J →L[ℝ] ℝ) ⊤ mu) :
    coefficientFormL mu i C = (TauCeti.lpBilinearForm mu C).bilinearComp i i := rfl
end General

/-- The actual fixed zero-boundary Sobolev value-gradient inclusion. -/
def unitBallJetL : BallH1Zero →L[ℝ]
    Lp (ℝ × R3) 2 ((volume : Measure R3).restrict ballOpens) :=
  (TauCeti.PDE.jetLpL (mu := (volume : Measure R3)) (Omega := ballOpens)).comp
    (TauCeti.w1p0Submodule volume ballOpens 2).toSubmodule.subtypeL

/-- The actual fixed-domain weak energy form as a continuous linear function of its coefficients. -/
def unitBallCoefficientFormL :=
  coefficientFormL (J := ℝ × R3) ((volume : Measure R3).restrict ballOpens) unitBallJetL

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_unitBallCoefficientForm {n : WithTop ℕ∞}
    (C : E → Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
      ((volume : Measure R3).restrict ballOpens)) (s : Set E)
    (hC : ContDiffOn ℝ n C s) :
    ContDiffOn ℝ n (fun x => unitBallCoefficientFormL (C x)) s :=
  unitBallCoefficientFormL.contDiff.comp_contDiffOn hC

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

theorem contDiffOn_unitBallCoefficientInverse {n : WithTop ℕ∞}
    (C : E → Lp ((ℝ × R3) →L[ℝ] (ℝ × R3) →L[ℝ] ℝ) ⊤
      ((volume : Measure R3).restrict ballOpens)) (s : Set E)
    (hC : ContDiffOn ℝ n C s)
    (hc : ∀ x ∈ s, IsCoercive (unitBallCoefficientFormL (C x))) :
    ContDiffOn ℝ n (fun x => functionalInverse (unitBallCoefficientFormL (C x))) s :=
  contDiffOn_functionalInverse (fun x => unitBallCoefficientFormL (C x)) s
    (contDiffOn_unitBallCoefficientForm C s hC) hc


end OAI.AnisotropicCalderon.DirichletFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.lpBilinearFormL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.lpBilinearFormL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.restrictBilinearL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.restrictBilinearL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.coefficientFormL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.coefficientFormL_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.unitBallJetL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.unitBallCoefficientFormL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.contDiffOn_unitBallCoefficientForm
#print axioms OAI.AnisotropicCalderon.DirichletFamily.contDiffOn_unitBallCoefficientInverse
