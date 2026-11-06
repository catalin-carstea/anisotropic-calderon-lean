import Calderon.SignedTaylorFixedLinearTransport
import Calderon.BoundedParameterSmoothness
import Calderon.FiniteDimensionalLocalSmoothExtension

/-! Upfront: general-boundary-multiplier-commutator-author-oct15-v001/
EXPANSION-smooth-signed-remainder-fixed-topology-v035.md. Joint smoothness
is derived in the genuine Banach topology from actual fixed-interval integration. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Function
open scoped ContDiff Topology BoundedContinuousFunction
namespace OAI.AnisotropicCalderon.ConnectionError
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def unitIntervalBoundedIntegralL : (ℝ →ᵇ V) →L[ℝ] V :=
  ({ toFun := fun f => ∫ a : ℝ in (0 : ℝ)..1, f a
     map_add' := by
       intro f g
       change (∫ a : ℝ in (0 : ℝ)..1, (f a+g a)) = _
       exact intervalIntegral.integral_add
         (f.continuous.intervalIntegrable 0 1) (g.continuous.intervalIntegrable 0 1)
     map_smul' := by
       intro c f
       change (∫ a : ℝ in (0 : ℝ)..1, c • f a) = c • (∫ a : ℝ in (0 : ℝ)..1, f a)
       exact intervalIntegral.integral_smul c _ } : (ℝ →ᵇ V) →ₗ[ℝ] V).mkContinuous 1
    (fun f => by
      change ‖∫ a : ℝ in (0 : ℝ)..1, f a‖ ≤ 1*‖f‖
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := (1 : ℝ)) (fun a ha => f.norm_coe_le_norm a)
      simpa only [sub_zero,abs_one,mul_one,one_mul] using hb)

lemma unitIntervalBoundedIntegralL_apply (f : ℝ →ᵇ V) :
    unitIntervalBoundedIntegralL f = ∫ a : ℝ in (0 : ℝ)..1, f a := rfl

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def smoothRadialSecondField (F : P × ℝ → V) (z : P × ℝ) : V :=
  fderiv ℝ (fun u : P × ℝ => fderiv ℝ F u (0,1)) z (0,1)

lemma contDiff_smoothRadialSecondField (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (smoothRadialSecondField F) :=
  (((hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiff_const

lemma smoothRadialSecondField_eq_slice_deriv_deriv
    (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) (p : P) (r : ℝ) :
    smoothRadialSecondField F (p,r) = deriv (deriv (fun t : ℝ => F (p,t))) r := by
  let e : P × ℝ := (0,1)
  have hc : HasDerivAt (fun t : ℝ => (p,t)) e r :=
    (hasDerivAt_const r p).prodMk (hasDerivAt_id r)
  have hEq : deriv (fun t : ℝ => F (p,t)) =ᶠ[𝓝 r]
      (fun t : ℝ => fderiv ℝ F (p,t) e) := by
    filter_upwards [] with t
    have ht : HasDerivAt (fun u : ℝ => (p,u)) e t :=
      (hasDerivAt_const t p).prodMk (hasDerivAt_id t)
    exact ((hF.differentiable (by simp) (p,t)).hasFDerivAt.comp_hasDerivAt t ht).deriv
  let G : P × ℝ → V := fun u => fderiv ℝ F u e
  have hGSmooth : ContDiff ℝ ∞ G :=
    (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hGDeriv := ((hGSmooth.differentiable (by simp) (p,r)).hasFDerivAt.comp_hasDerivAt r hc).deriv
  have hSecond := hEq.deriv_eq.trans hGDeriv
  simpa only [Function.comp_def,smoothRadialSecondField,G,e] using hSecond.symm

lemma contDiff_secondTaylorRemainder_joint
    {P0 V0 : Type} [NormedAddCommGroup P0] [NormedSpace ℝ P0]
    [NormedAddCommGroup V0] [NormedSpace ℝ V0] [CompleteSpace V0]
    (F : P0 × ℝ → V0) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : P0 × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2) := by
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 := by
    intro a ha
    constructor <;> linarith [ha.1,ha.2]
  obtain ⟨χ,hχ,_,hSupport,hOne⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) isOpen_Ioo isClosed_Icc hsub
  let W : (P0 × ℝ) × ℝ → V0 := fun z =>
    (χ z.2*(1-z.2)) • smoothRadialSecondField F (z.1.1,z.2*z.1.2)
  have hW : ContDiff ℝ ∞ W :=
    ((hχ.comp contDiff_snd).mul (contDiff_const.sub contDiff_snd)).smul
      ((contDiff_smoothRadialSecondField F hF).comp
        (contDiff_fst.fst.prodMk (contDiff_snd.mul contDiff_fst.snd)))
  have hz : ∀ z a, a ∉ Icc (-1 : ℝ) 2 → W (z,a) = 0 := by
    intro z a ha
    have hc : χ a = 0 := by
      apply notMem_support.mp
      rw [hSupport]
      intro hmem
      exact ha ⟨hmem.1.le,hmem.2.le⟩
    simp only [W,hc,zero_mul,zero_smul]
  have hSlices : ContDiff ℝ ∞
      (CommonSupportSlices.commonSupportSlice W hW.continuous (Icc (-1 : ℝ) 2) isCompact_Icc hz) :=
    BoundedParameterSmoothness.contDiff_infty_commonSupportSlice
      (H := P0 × ℝ) (V := ℝ) (E := V0) W hW (Icc (-1 : ℝ) 2) isCompact_Icc hz
  let BInt : (ℝ →ᵇ V0) →L[ℝ] V0 := unitIntervalBoundedIntegralL
  have hBInt : ContDiff ℝ ∞ BInt := BInt.contDiff
  have hInt : ContDiff ℝ ∞ (fun z : P0 × ℝ => unitIntervalBoundedIntegralL
      (CommonSupportSlices.commonSupportSlice W hW.continuous (Icc (-1 : ℝ) 2) isCompact_Icc hz z)) :=
    hBInt.comp hSlices
  have he : (fun z : P0 × ℝ => unitIntervalBoundedIntegralL
      (CommonSupportSlices.commonSupportSlice W hW.continuous (Icc (-1 : ℝ) 2) isCompact_Icc hz z)) =
      fun z : P0 × ℝ => secondTaylorRemainder (fun t : ℝ => F (z.1,t)) z.2 := by
    funext z
    rw [unitIntervalBoundedIntegralL_apply]
    apply intervalIntegral.integral_congr
    intro a ha
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ha
    have hc : χ a = 1 := (hOne a).mp ha
    change (χ a*(1-a)) • smoothRadialSecondField F (z.1,a*z.2) =
      (1-a) • deriv (deriv (fun t : ℝ => F (z.1,t))) (a*z.2)
    rw [hc,one_mul,smoothRadialSecondField_eq_slice_deriv_deriv F hF]
  rw [← he]
  exact hInt

end OAI.AnisotropicCalderon.ConnectionError

#print axioms OAI.AnisotropicCalderon.ConnectionError.unitIntervalBoundedIntegralL
#print axioms OAI.AnisotropicCalderon.ConnectionError.unitIntervalBoundedIntegralL_apply
#print axioms OAI.AnisotropicCalderon.ConnectionError.smoothRadialSecondField
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_smoothRadialSecondField
#print axioms OAI.AnisotropicCalderon.ConnectionError.smoothRadialSecondField_eq_slice_deriv_deriv
#print axioms OAI.AnisotropicCalderon.ConnectionError.contDiff_secondTaylorRemainder_joint
