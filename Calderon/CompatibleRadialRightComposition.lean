import Mathlib.Analysis.Normed.Operator.Basic
set_option autoImplicit false
namespace OAI.AnisotropicCalderon.RadialEndpointCompatibility
lemma compatible_sum_sub_right_composition
    {Xh Xl Yh Yl : Type*}
    [NormedAddCommGroup Xh] [NormedSpace ℝ Xh]
    [NormedAddCommGroup Xl] [NormedSpace ℝ Xl]
    [NormedAddCommGroup Yh] [NormedSpace ℝ Yh]
    [NormedAddCommGroup Yl] [NormedSpace ℝ Yl]
    (Nh Bh Th : Xh →L[ℝ] Yh) (Nl Bl Tl : Xl →L[ℝ] Yl)
    (H : Xh →L[ℝ] Xh) (L : Xl →L[ℝ] Xl) (I : Xh →L[ℝ] Xl) (J : Yh →L[ℝ] Yl)
    (hN : J.comp Nh = Nl.comp I) (hB : J.comp Bh = Bl.comp I)
    (hT : J.comp Th = Tl.comp I) (hH : I.comp H = L.comp I) :
    J.comp ((Nh+Bh-Th).comp H) = ((Nl+Bl-Tl).comp L).comp I := by
  apply ContinuousLinearMap.ext
  intro u
  have hNp : J (Nh (H u)) = Nl (I (H u)) := congrArg (fun T : Xh →L[ℝ] Yl => T (H u)) hN
  have hBp : J (Bh (H u)) = Bl (I (H u)) := congrArg (fun T : Xh →L[ℝ] Yl => T (H u)) hB
  have hTp : J (Th (H u)) = Tl (I (H u)) := congrArg (fun T : Xh →L[ℝ] Yl => T (H u)) hT
  have hHp : I (H u) = L (I u) := congrArg (fun T : Xh →L[ℝ] Xl => T u) hH
  change J (Nh (H u)+Bh (H u)-Th (H u)) = Nl (L (I u))+Bl (L (I u))-Tl (L (I u))
  rw [map_sub,map_add,hNp,hBp,hTp,hHp]
end OAI.AnisotropicCalderon.RadialEndpointCompatibility
#print axioms OAI.AnisotropicCalderon.RadialEndpointCompatibility.compatible_sum_sub_right_composition
