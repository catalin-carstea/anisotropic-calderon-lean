import Calderon.QradFourIndexWeakForm
import Calderon.SphereSobolevPairingInclusion
import Mathlib.Analysis.InnerProductSpace.Basic

/-! Exact four-index pivot cancellation on genuine first-output representatives.
All physical graph premises are explicit hypotheses. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JH" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "ZH" => sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
local notation "P" => sphereSobolevDualPairing (-(1/2 : ℝ))
attribute [local irreducible] sphereSobolevInclusionL sphereSobolevDualPairing qradFourIndexWeakForm

variable (RH LH : Fin 3 → Hi →L[ℝ] Half) (RL LL : Fin 3 → Half →L[ℝ] Neg)
  (CH : Fin 3 → Fin 3 → Hi →L[ℝ] Half) (CL : Fin 3 → Fin 3 → Half →L[ℝ] Neg)
  (hR : ∀ i v, JH (RH i v) = RL i (IH v))
  (hL : ∀ i v, JH (LH i v) = LL i (IH v))
  (hC : ∀ i k v, JH (CH i k v) = CL i k (IH v))
  (hBracket : ∀ i k v, CL i k (IH v) = LL i (RH k v) - RL k (LH i v))
  (hLAdj : ∀ i (z : Half) (v : Hi), P (LL i z) (IH v) = ⟪ZH z,ZH (RH i v)⟫_ℝ)
  (hRAdj : ∀ i (z : Half) (v : Hi), P (RL i z) (IH v) = ⟪ZH z,ZH (LH i v)⟫_ℝ)

include hR hL hC hBracket in
lemma qradAdjacentHigh_eq_on_first_output_representatives
    (u : Hi) (r l : Fin 3 → Hi) (hr : ∀ i, IH (r i) = RH i u)
    (hl : ∀ i, IH (l i) = LH i u) (i k : Fin 3) :
    CH i k u = LH i (r k) - RH k (l i) := by
  apply sphereSobolevInclusionL_injective (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
  have hFirst : JH (LH i (r k)) = LL i (RH k u) :=
    (hL i (r k)).trans (congrArg (LL i) (hr k))
  have hSecond : JH (RH k (l i)) = RL k (LH i u) :=
    (hR k (l i)).trans (congrArg (RL k) (hl i))
  calc
    _ = CL i k (IH u) := hC i k u
    _ = LL i (RH k u) - RL k (LH i u) := hBracket i k u
    _ = JH (LH i (r k)) - JH (RH k (l i)) :=
      congrArg₂ (fun a b : Neg => a-b) hFirst.symm hSecond.symm
    _ = _ := ((JH).map_sub _ _).symm

include hBracket hLAdj hRAdj in
lemma qradAdjacentPairing_eq_crossGram (i k : Fin 3) (v w : Hi) :
    P (CL i k (IH v)) (IH w) =
      ⟪ZH (RH k v),ZH (RH i w)⟫_ℝ - ⟪ZH (LH i v),ZH (LH k w)⟫_ℝ := by
  have hEq := congrArg (fun z : Neg => P z (IH w)) (hBracket i k v)
  have hSplit : P (LL i (RH k v) - RL k (LH i v)) (IH w) =
      P (LL i (RH k v)) (IH w) - P (RL k (LH i v)) (IH w) := by
    unfold sphereSobolevDualPairing
    exact inner_sub_left (𝕜 := ℝ) _ _ _
  exact hEq.trans (hSplit.trans
    (congrArg₂ (fun a b : ℝ => a-b) (hLAdj i (RH k v) w) (hRAdj k (LH i v) w)))

include hR hL hC hBracket hLAdj hRAdj in
theorem qradFourIndexWeakForm_eq_second_output_gram_difference
    (u : Hi) (r l : Fin 3 → Hi) (hr : ∀ i, IH (r i) = RH i u)
    (hl : ∀ i, IH (l i) = LH i u) (i j k s : Fin 3) :
    qradFourIndexWeakForm RH LH LL CH CL i j k s u =
      ⟪ZH (RH i (r j)),ZH (RH k (r s))⟫_ℝ -
        ⟪ZH (LH j (l i)),ZH (LH s (l k))⟫_ℝ := by
  have hRep (a b : Fin 3) : CH a b u = LH a (r b) - RH b (l a) :=
    qradAdjacentHigh_eq_on_first_output_representatives
      RH LH RL LL CH CL hR hL hC hBracket u r l hr hl a b
  have h1 : P (CL i k (RH s u)) (RH j u) =
      ⟪ZH (RH k (r s)),ZH (RH i (r j))⟫_ℝ -
        ⟪ZH (LH i (r s)),ZH (LH k (r j))⟫_ℝ :=
    (congrArg₂ (fun a b : Half => P (CL i k a) b) (hr s).symm (hr j).symm).trans
      (qradAdjacentPairing_eq_crossGram RH LH RL LL CL hBracket hLAdj hRAdj i k (r s) (r j))
  have h4 : P (CL j s (LH i u)) (LH k u) =
      ⟪ZH (RH s (l i)),ZH (RH j (l k))⟫_ℝ -
        ⟪ZH (LH j (l i)),ZH (LH s (l k))⟫_ℝ :=
    (congrArg₂ (fun a b : Half => P (CL j s a) b) (hl i).symm (hl k).symm).trans
      (qradAdjacentPairing_eq_crossGram RH LH RL LL CL hBracket hLAdj hRAdj j s (l i) (l k))
  have h2 : P (LL i (RH s u)) (CH k j u) =
      ⟪ZH (LH i (r s)),ZH (LH k (r j))⟫_ℝ -
        ⟪ZH (LH i (r s)),ZH (RH j (l k))⟫_ℝ := by
    have hCompat : JH (LH i (r s)) = LL i (RH s u) :=
      (hL i (r s)).trans (congrArg (LL i) (hr s))
    calc
      _ = P (JH (LH i (r s))) (CH k j u) :=
        congrArg (fun z : Neg => P z (CH k j u)) hCompat.symm
      _ = ⟪ZH (LH i (r s)),ZH (CH k j u)⟫_ℝ :=
        sphereSobolevDualPairing_inclusion_eq_inner_zero (1/2 : ℝ) (by norm_num) _ _
      _ = _ := by
        have hZ : ZH (CH k j u) = ZH (LH k (r j)) - ZH (RH j (l k)) :=
          (congrArg (ZH) (hRep k j)).trans ((ZH).map_sub _ _)
        exact (congrArg (fun z : SphereSobolev 0 => ⟪ZH (LH i (r s)),z⟫_ℝ) hZ).trans
          (inner_sub_right _ _ _)
  have h3 : P (LL j (CH i s u)) (LH k u) =
      ⟪ZH (LH i (r s)),ZH (RH j (l k))⟫_ℝ -
        ⟪ZH (RH s (l i)),ZH (RH j (l k))⟫_ℝ := by
    calc
      _ = P (LL j (CH i s u)) (IH (l k)) :=
        congrArg (fun z : Half => P (LL j (CH i s u)) z) (hl k).symm
      _ = ⟪ZH (CH i s u),ZH (RH j (l k))⟫_ℝ := hLAdj j (CH i s u) (l k)
      _ = _ := by
        have hZ : ZH (CH i s u) = ZH (LH i (r s)) - ZH (RH s (l i)) :=
          (congrArg (ZH) (hRep i s)).trans ((ZH).map_sub _ _)
        exact (congrArg (fun z : SphereSobolev 0 => ⟪z,ZH (RH j (l k))⟫_ℝ) hZ).trans
          (inner_sub_left _ _ _)
  have hSym := real_inner_comm (ZH (RH k (r s))) (ZH (RH i (r j)))
  have hTerms := congrArg₂ (fun a b : ℝ => a+b)
    (congrArg₂ (fun a b : ℝ => a+b) (congrArg₂ (fun a b : ℝ => a+b) h1 h2) h3) h4
  unfold qradFourIndexWeakForm
  exact hTerms.trans (by linarith only [hSym])

end OAI.AnisotropicCalderon.SphereHarmonic
