import Calderon.ActualLowerUSWeakAngularWords

/-!
Author: GPT-6.1 Sol, author support only.
Before-code: ../lower-r-z-quadratic-leibniz-upfront.md.
One narrowly typed weak two-word telescoping identity. The concrete producer
must supply its graph identities from actual same-germ endpoint rooms.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSWeakAngularWords
open SphereHarmonic ActualAngularPiDraft
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)

/-- An adjunction identity on genuine high tests extends to all Half tests by
the canonical dense inclusion. No inverse Sobolev inclusion is used. -/
lemma low_adjunction_of_high_test (A Asharp : Half →L[ℝ] Neg)
    (h : ∀ u : Hi, ∀ z : Half, PP (IH u) (A z) = PP z (Asharp (IH u))) :
    ∀ u z : Half, PP u (A z) = PP z (Asharp u) := by
  intro u z
  let Left : Half → ℝ := fun a => PP a (A z)
  let Right : Half → ℝ := fun a => PP z (Asharp a)
  have hL : Continuous Left := continuous_id.inner continuous_const
  have hR : Continuous Right := continuous_const.inner Asharp.continuous
  have he : Left = Right :=
    (denseRange_sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)).equalizer
      hL hR (funext (fun a => h a z))
  exact congrFun he u

/-- G against an ordered E1 E2 word, expressed entirely on the actual high/low
levels. The left gain's true adjoint high map is explicit as C1sharp. -/
lemma weak_quadratic_word_leibniz
    (G Gsharp : Hi →L[ℝ] Half) (Gl Gsharpl : Half →L[ℝ] Neg)
    (E1 E2 e1 : Hi →L[ℝ] Half) (E1l E2l e1l : Half →L[ℝ] Neg)
    (C1 C1sharp C2 : Hi →L[ℝ] Half) (C1l : Half →L[ℝ] Neg)
    (hG : ∀ a b : Half, PP a (Gl b) = PP b (Gsharpl a))
    (hE1 : ∀ a b : Half, PP a (E1l b) = PP b (e1l a))
    (he1 : ∀ a : Hi, e1l (IH a) = JL (e1 a))
    (hE2 : ∀ a : Hi, JL (E2 a) = E2l (IH a))
    (hC1 : ∀ a : Hi, ∀ z : Half, PP (IH a) (C1l z) = PP (C1sharp a) (JL z))
    (hC1sharp : ∀ a : Hi, JL (C1sharp a) = e1l (Gsharp a)-Gsharpl (e1 a))
    (hC2 : ∀ a : Hi, JL (C2 a) = Gl (E2 a)-E2l (G a))
    (u v uGsharp vG : Hi) (hu : IH uGsharp = Gsharp u) (hv : IH vG = G v) :
    PP (IH uGsharp) (E1l (E2 v)) - PP (IH u) (E1l (E2 vG)) =
      PP (IH u) ((C1l.comp E2 + E1l.comp C2) v) := by
  have hS : e1l (Gsharp u) = Gsharpl (e1 u)+JL (C1sharp u) := by
    rw [hC1sharp]
    abel
  have hLeft : PP (IH uGsharp) (E1l (E2 v)) =
      PP (e1 u) (Gl (E2 v)) + PP (C1sharp u) (JL (E2 v)) := by
    calc
      _ = PP (E2 v) (e1l (IH uGsharp)) := hE1 _ _
      _ = PP (E2 v) (e1l (Gsharp u)) := congrArg (fun z : Half => PP (E2 v) (e1l z)) hu
      _ = PP (E2 v) (Gsharpl (e1 u)+JL (C1sharp u)) := congrArg (fun z : Neg => PP (E2 v) z) hS
      _ = PP (E2 v) (Gsharpl (e1 u))+PP (E2 v) (JL (C1sharp u)) := inner_add_right _ _ _
      _ = _ := congrArg₂ (fun a b : ℝ => a+b)
        (hG (e1 u) (E2 v)).symm (v016_pairing_inclusion_symm (E2 v) (C1sharp u))
  have hRight : PP (IH u) (E1l (E2 vG)) = PP (e1 u) (E2l (G v)) := by
    calc
      _ = PP (E2 vG) (e1l (IH u)) := hE1 _ _
      _ = PP (E2 vG) (JL (e1 u)) := congrArg (fun z : Neg => PP (E2 vG) z) (he1 u)
      _ = PP (e1 u) (JL (E2 vG)) := v016_pairing_inclusion_symm _ _
      _ = PP (e1 u) (E2l (IH vG)) := congrArg (fun z : Neg => PP (e1 u) z) (hE2 vG)
      _ = _ := congrArg (fun z : Half => PP (e1 u) (E2l z)) hv
  have hGain2 : PP (e1 u) (Gl (E2 v))-PP (e1 u) (E2l (G v)) =
      PP (IH u) (E1l (C2 v)) := by
    symm
    calc
      _ = PP (C2 v) (e1l (IH u)) := hE1 _ _
      _ = PP (C2 v) (JL (e1 u)) := congrArg (fun z : Neg => PP (C2 v) z) (he1 u)
      _ = PP (e1 u) (JL (C2 v)) := v016_pairing_inclusion_symm _ _
      _ = PP (e1 u) (Gl (E2 v)-E2l (G v)) := congrArg (fun z : Neg => PP (e1 u) z) (hC2 v)
      _ = _ := inner_sub_right _ _ _
  have hGain1 : PP (C1sharp u) (JL (E2 v)) = PP (IH u) (C1l (E2 v)) :=
    (hC1 u (E2 v)).symm
  have hResult : PP (IH u) ((C1l.comp E2 + E1l.comp C2) v) =
      PP (IH u) (C1l (E2 v))+PP (IH u) (E1l (C2 v)) := by
    exact inner_add_right (IH u) (C1l (E2 v)) (E1l (C2 v))
  linarith only [hLeft,hRight,hGain1,hGain2,hResult]


lemma norm_weak_quadratic_word_le (E2 C2 : Hi →L[ℝ] Half)
    (C1l E1l : Half →L[ℝ] Neg) :
    ‖C1l.comp E2 + E1l.comp C2‖ ≤ ‖C1l‖*‖E2‖+‖E1l‖*‖C2‖ :=
  (norm_add_le (C1l.comp E2) (E1l.comp C2)).trans (add_le_add
    (ContinuousLinearMap.opNorm_comp_le C1l E2) (ContinuousLinearMap.opNorm_comp_le E1l C2))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualLowerUSWeakAngularWords
