import Calderon.SphereSobolevInclusion
set_option autoImplicit false
noncomputable section
namespace OAI.AnisotropicCalderon.SphereHarmonic
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Ihi" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "Jlo" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local irreducible] sphereSobolevInclusionL

lemma adjacentGainedLow_eq_bracket_of_native_graphs
    (Sh Th Gk : Hi →L[ℝ] Half) (Sl Tl K Gn : Half →L[ℝ] Neg)
    (MHk : Hi →L[ℝ] Hi) (MLi MLk : Half →L[ℝ] Half) (MNi MNk : Neg →L[ℝ] Neg)
    (hK : ∀ v, K (Ihi v) = Tl (Sh v) - Sl (Th v))
    (hG : ∀ v, Gk v = Sh (MHk v) - MLk (Sh v))
    (hGn : ∀ z, Gn (Jlo z) = Tl (MLi z) - MNi (Tl z))
    (hSl : ∀ v, Sl (Ihi v) = Jlo (Sh v))
    (hML : ∀ z, Jlo (MLk z) = MNk (Jlo z))
    (hMH : ∀ v, Ihi (MHk v) = MLk (Ihi v))
    (hComm : ∀ z, MLi (MLk z) = MLk (MLi z)) (u : Hi) :
    -MNi (K (MLk (Ihi u))) + MNi (Tl (Gk u)) - Gn (MNk (Sl (Ihi u))) =
      MNi (Sl (Th (MHk u))) - Tl (MLk (MLi (Sh u))) := by
  have hFirst : K (MLk (Ihi u)) = Tl (Sh (MHk u)) - Sl (Th (MHk u)) :=
    (congrArg K (hMH u).symm).trans (hK (MHk u))
  have hArg : MNk (Sl (Ihi u)) = Jlo (MLk (Sh u)) :=
    (congrArg MNk (hSl u)).trans (hML (Sh u)).symm
  have hLast : Gn (MNk (Sl (Ihi u))) = Tl (MLi (MLk (Sh u))) - MNi (Tl (MLk (Sh u))) :=
    (congrArg Gn hArg).trans (hGn (MLk (Sh u)))
  have hTotal := congrArg₂ (fun a b : Neg => a-b)
    (congrArg₂ (fun a b : Neg => a+b)
      (congrArg (fun z : Neg => -MNi z) hFirst)
      (congrArg (fun z : Half => MNi (Tl z)) (hG u))) hLast
  calc
    _ = -MNi (Tl (Sh (MHk u)) - Sl (Th (MHk u))) +
        MNi (Tl (Sh (MHk u) - MLk (Sh u))) -
        (Tl (MLi (MLk (Sh u))) - MNi (Tl (MLk (Sh u)))) := hTotal
    _ = MNi (Sl (Th (MHk u))) - Tl (MLi (MLk (Sh u))) := by
      simp only [map_sub]
      abel
    _ = _ := congrArg₂ (fun a b : Neg => a-b) rfl
      (congrArg Tl (hComm (Sh u)))
end OAI.AnisotropicCalderon.SphereHarmonic
