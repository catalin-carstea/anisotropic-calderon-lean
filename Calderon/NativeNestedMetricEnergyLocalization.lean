import Calderon.NativeNestedZeroBoundaryReplacement
import Calderon.MetricSmooth

/-! EXPANSION.json precedes literal nested-native metric energy/source localization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

lemma setIntegral_difference_eq_inner (Omega OmegaOuter : Opens R3) (hsub : Omega ≤ OmegaOuter)
    (f g : R3 → ℝ) (hf : IntegrableOn f OmegaOuter (volume : Measure R3))
    (hg : IntegrableOn g OmegaOuter (volume : Measure R3))
    (hOutside : ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter,
      x ∉ (Omega : Set R3) → f x = g x) :
    (∫ x in OmegaOuter, f x ∂(volume : Measure R3)) - ∫ x in OmegaOuter, g x ∂volume =
      (∫ x in Omega, f x ∂(volume : Measure R3)) - ∫ x in Omega, g x ∂volume := by
  have hsubset : (Omega : Set R3) ⊆ OmegaOuter := SetLike.coe_subset_coe.mpr hsub
  have hDiffOutside : ∀ᵐ x ∂(volume : Measure R3).restrict ((OmegaOuter : Set R3) \ Omega),
      x ∉ (Omega : Set R3) → f x = g x := hOutside.filter_mono
    (ae_mono (Measure.restrict_mono_set (volume : Measure R3) sdiff_subset))
  have hzAE : (fun x => f x - g x) =ᵐ[
      (volume : Measure R3).restrict ((OmegaOuter : Set R3) \ Omega)] fun _ => 0 := by
    filter_upwards [hDiffOutside,
      ae_restrict_mem (OmegaOuter.isOpen.measurableSet.diff Omega.isOpen.measurableSet)]
      with x hx hxMem
    exact sub_eq_zero.mpr (hx hxMem.2)
  have hz : (∫ x in (OmegaOuter : Set R3) \ Omega, (f x-g x) ∂(volume : Measure R3)) = 0 := by
    simpa only [integral_zero] using integral_congr_ae hzAE
  have hSplit := setIntegral_sdiff Omega.isOpen.measurableSet (hf.sub hg) hsubset
  have hEqual := sub_eq_zero.mp (hSplit.symm.trans hz)
  simpa only [Pi.sub_apply, integral_sub hf hg, integral_sub (hf.mono_set hsubset) (hg.mono_set hsubset)] using hEqual

lemma energyFormH1_restrict_eq_setIntegral (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter) (A : MatrixField)
    (U V : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) :
    TauCeti.PDE.energyFormH1 A 0 0 (TauCeti.W1p.restrictL hsub U)
      (TauCeti.W1p.restrictL hsub V) =
    ∫ x in Omega, TauCeti.PDE.energyIntegrand (A x) 0 0
      (TauCeti.PDE.jetField U x) (TauCeti.PDE.jetField V x) ∂(volume : Measure R3) := by
  rw [TauCeti.PDE.energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [TauCeti.W1p.value_restrictL_ae hsub U,
    TauCeti.W1p.gradient_restrictL_ae hsub U, TauCeti.W1p.value_restrictL_ae hsub V,
    TauCeti.W1p.gradient_restrictL_ae hsub V] with x hu hdu hv hdv
  simp only [TauCeti.PDE.jetField_apply,hu,hdu,hv,hdv,Pi.zero_apply]

lemma metricReplacement_energyDensity_eq_outside (OmegaOuter : Opens R3)
    (hsub : ballOpens ≤ OmegaOuter) (g₁ g₂ : MatrixField)
    (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (W : TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2) (z : BallH1Zero) :
    ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter, x ∉ (ballOpens : Set R3) →
      TauCeti.PDE.energyIntegrand (principalCoefficient g₂ x) 0 0
        (TauCeti.PDE.jetField
          (nativeZeroBoundaryReplacement ballOpens OmegaOuter hsub W z :
            TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x)
        (TauCeti.PDE.jetField
          (nativeZeroBoundaryReplacement ballOpens OmegaOuter hsub W z :
            TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x) =
      TauCeti.PDE.energyIntegrand (principalCoefficient g₁ x) 0 0
        (TauCeti.PDE.jetField (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x)
        (TauCeti.PDE.jetField (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x) := by
  filter_upwards [nativeZeroBoundaryReplacement_value_eq_outside ballOpens OmegaOuter hsub W z,
    nativeZeroBoundaryReplacement_gradient_eq_outside ballOpens OmegaOuter hsub W z]
    with x hv hd hx
  have hxNorm : 1 ≤ ‖x‖ := by
    have hNot : ¬ ‖x‖ < 1 := by
      change x ∉ Metric.ball (0 : R3) 1 at hx
      simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact le_of_not_gt hNot
  simp only [TauCeti.PDE.jetField_apply, hv hx, hd hx,
    principalCoefficient_eq_one_of_exterior g₁ hg₁ x hxNorm,
    principalCoefficient_eq_one_of_exterior g₂ hg₂ x hxNorm]

lemma metricReplacement_energy_difference_eq_inner (OmegaOuter : Opens R3)
    (hsub : ballOpens ≤ OmegaOuter) (g₁ g₂ : MatrixField)
    (hg₁ : IsAdmissibleMetric g₁) (hg₂ : IsAdmissibleMetric g₂)
    (hc₁ : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g₁ x) 0 0) ⊤
      ((volume : Measure R3).restrict OmegaOuter))
    (hc₂ : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g₂ x) 0 0) ⊤
      ((volume : Measure R3).restrict OmegaOuter))
    (W : TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2) (z : BallH1Zero) :
    let U := (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2)
    let V := (nativeZeroBoundaryReplacement ballOpens OmegaOuter hsub W z :
      TauCeti.W1p (volume : Measure R3) OmegaOuter 2)
    TauCeti.PDE.energyFormH1 (principalCoefficient g₂) 0 0 V V -
      TauCeti.PDE.energyFormH1 (principalCoefficient g₁) 0 0 U U =
    TauCeti.PDE.energyFormH1 (principalCoefficient g₂) 0 0
      (TauCeti.W1p.restrictL hsub V) (TauCeti.W1p.restrictL hsub V) -
    TauCeti.PDE.energyFormH1 (principalCoefficient g₁) 0 0
      (TauCeti.W1p.restrictL hsub U) (TauCeti.W1p.restrictL hsub U) := by
  dsimp only
  let U : TauCeti.W1p (volume : Measure R3) OmegaOuter 2 := W
  let V : TauCeti.W1p (volume : Measure R3) OmegaOuter 2 :=
    nativeZeroBoundaryReplacement ballOpens OmegaOuter hsub W z
  let D₁ : R3 → ℝ := fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g₁ x) 0 0
    (TauCeti.PDE.jetField U x) (TauCeti.PDE.jetField U x)
  let D₂ : R3 → ℝ := fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g₂ x) 0 0
    (TauCeti.PDE.jetField V x) (TauCeti.PDE.jetField V x)
  have hInt₁ : IntegrableOn D₁ OmegaOuter (volume : Measure R3) :=
    TauCeti.PDE.integrable_energyIntegrand_jetField hc₁ U U
  have hInt₂ : IntegrableOn D₂ OmegaOuter (volume : Measure R3) :=
    TauCeti.PDE.integrable_energyIntegrand_jetField hc₂ V V
  have hOutside : ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter,
      x ∉ (ballOpens : Set R3) → D₂ x = D₁ x :=
    metricReplacement_energyDensity_eq_outside OmegaOuter hsub g₁ g₂ hg₁ hg₂ W z
  have hLoc := setIntegral_difference_eq_inner ballOpens OmegaOuter hsub D₂ D₁ hInt₂ hInt₁ hOutside
  have hOuter := congrArg₂ (fun s t : ℝ => s-t)
    (TauCeti.PDE.energyFormH1_def (principalCoefficient g₂) 0 0 V V)
    (TauCeti.PDE.energyFormH1_def (principalCoefficient g₁) 0 0 U U)
  have hInner := congrArg₂ (fun s t : ℝ => s-t)
    (energyFormH1_restrict_eq_setIntegral ballOpens OmegaOuter hsub (principalCoefficient g₂) V V)
    (energyFormH1_restrict_eq_setIntegral ballOpens OmegaOuter hsub (principalCoefficient g₁) U U)
  exact hOuter.trans (hLoc.trans hInner.symm)

lemma nativeZeroBoundaryReplacement_source_pairing_eq (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter)
    (W : TauCeti.W1p0 (volume : Measure R3) OmegaOuter 2)
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) (F : R3 → ℝ)
    (hZero : ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter, x ∈ (Omega : Set R3) → F x = 0) :
    (∫ x in OmegaOuter, F x * TauCeti.W1p.value
      (nativeZeroBoundaryReplacement Omega OmegaOuter hsub W z :
        TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x ∂(volume : Measure R3)) =
    ∫ x in OmegaOuter, F x * TauCeti.W1p.value
      (W : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) x ∂(volume : Measure R3) := by
  apply integral_congr_ae
  filter_upwards [nativeZeroBoundaryReplacement_value_eq_outside Omega OmegaOuter hsub W z,
    hZero] with x hx hF
  by_cases hMem : x ∈ (Omega : Set R3)
  · rw [hF hMem,zero_mul,zero_mul]
  · rw [hx hMem]

end OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.setIntegral_difference_eq_inner
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.energyFormH1_restrict_eq_setIntegral
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.metricReplacement_energyDensity_eq_outside
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.metricReplacement_energy_difference_eq_inner
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.nativeZeroBoundaryReplacement_source_pairing_eq
