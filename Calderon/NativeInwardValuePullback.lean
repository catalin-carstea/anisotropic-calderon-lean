import Calderon.NativeH1InwardDilation
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-! EXPANSION.json precedes this exact value/restriction bridge.
All measures and native norms remain literal. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal ContDiff Gradient Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

theorem quasiMeasurePreserving_unitBall_inwardDilation
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    QuasiMeasurePreserving (fun x : R3 => a • x)
      ((volume : Measure R3).restrict ballOpens) ((volume : Measure R3).restrict ballOpens) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  apply (quasiMeasurePreserving_smul (μ := (volume : Measure R3)) ha0.ne').restrict
  intro x hx
  have hxNorm : ‖x‖ < 1 := by
    simpa only [coe_ballOpens,B,mem_ball,dist_zero_right] using hx
  change a • x ∈ ball (0 : R3) 1
  rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right ha1 (norm_nonneg x))
    (by simpa only [one_mul] using hxNorm)

theorem memLp_unitBall_value_inwardDilation
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1)
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    MemLp (fun x : R3 => f (a • x)) 2 ((volume : Measure R3).restrict ballOpens) := by
  have hBound := eLpNorm_unitBall_inwardDilation_le_four (f : R3 → ℝ) a ha ha1
  have hAE : AEStronglyMeasurable (fun x : R3 => f (a • x))
      ((volume : Measure R3).restrict ballOpens) :=
    (Lp.memLp f).aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_unitBall_inwardDilation a ha ha1)
  have hFinite : eLpNorm (fun x : R3 => f (a • x)) 2
      ((volume : Measure R3).restrict ballOpens) < ⊤ :=
    lt_of_le_of_lt hBound (lt_top_iff_ne_top.mpr
      (ENNReal.mul_ne_top (by norm_num) (Lp.memLp f).eLpNorm_ne_top))
  unfold MemLp
  exact hFinite

theorem norm_unitBall_value_inwardDilation_toLp_le_four
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1)
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    ‖(memLp_unitBall_value_inwardDilation a ha ha1 f).toLp (fun x : R3 => f (a • x))‖ ≤
      4 * ‖f‖ := by
  have hBound := eLpNorm_unitBall_inwardDilation_le_four (f : R3 → ℝ) a ha ha1
  have hReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) (Lp.memLp f).eLpNorm_ne_top) hBound
  rw [Lp.norm_def,eLpNorm_congr_ae (MemLp.coeFn_toLp
    (memLp_unitBall_value_inwardDilation a ha ha1 f)),Lp.norm_def]
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] using hReal

def nativeUnitBallValueInwardDilation
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →L[ℝ]
      Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := by
  let Q := quasiMeasurePreserving_unitBall_inwardDilation a ha ha1
  let D : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) →ₗ[ℝ]
      Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    { toFun := fun f => (memLp_unitBall_value_inwardDilation a ha ha1 f).toLp
        (fun x : R3 => f (a • x))
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_unitBall_value_inwardDilation a ha ha1 (f+g)),
          MemLp.coeFn_toLp (memLp_unitBall_value_inwardDilation a ha ha1 f),
          MemLp.coeFn_toLp (memLp_unitBall_value_inwardDilation a ha ha1 g),
          Lp.coeFn_add
            ((memLp_unitBall_value_inwardDilation a ha ha1 f).toLp (fun x : R3 => f (a • x)))
            ((memLp_unitBall_value_inwardDilation a ha ha1 g).toLp (fun x : R3 => g (a • x))),
          Q.ae_eq_comp (Lp.coeFn_add f g)] with x hfg hf hg hAdd hComp
        change (f+g) (a • x) = f (a • x) + g (a • x) at hComp
        simpa only [Function.comp_apply,Pi.add_apply] using
          (hfg.trans hComp).trans ((hAdd.trans (congrArg₂ (fun r s : ℝ => r+s) hf hg)).symm)
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_unitBall_value_inwardDilation a ha ha1 (c • f)),
          MemLp.coeFn_toLp (memLp_unitBall_value_inwardDilation a ha ha1 f),
          Lp.coeFn_smul c
            ((memLp_unitBall_value_inwardDilation a ha ha1 f).toLp (fun x : R3 => f (a • x))),
          Q.ae_eq_comp (Lp.coeFn_smul c f)] with x hcf hf hSmul hComp
        change (c • f) (a • x) = c * f (a • x) at hComp
        simpa only [RingHom.id_apply,Function.comp_apply,Pi.smul_apply,smul_eq_mul] using
          (hcf.trans hComp).trans ((hSmul.trans (congrArg (fun r : ℝ => c*r) hf)).symm) }
  exact D.mkContinuous 4 (fun f => norm_unitBall_value_inwardDilation_toLp_le_four a ha ha1 f)

theorem nativeUnitBallValueInwardDilation_apply_ae
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1)
    (f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    (nativeUnitBallValueInwardDilation a ha ha1 f : R3 → ℝ)
      =ᵐ[((volume : Measure R3).restrict ballOpens)] (fun x : R3 => f (a • x)) := by
  exact MemLp.coeFn_toLp (memLp_unitBall_value_inwardDilation a ha ha1 f)

theorem value_nativeH1InwardDilation_eq_valueInwardDilation
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) (u : BallH1) :
    TauCeti.W1p.value (nativeH1InwardDilation a u) =
      nativeUnitBallValueInwardDilation a ha ha1 (TauCeti.W1p.value u) := by
  let V : BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := TauCeti.W1p.valueL
  let L : BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    V.comp (nativeH1InwardDilation a)
  let R : BallH1 →L[ℝ] Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    (nativeUnitBallValueInwardDilation a ha ha1).comp V
  have hSmooth (f : nativeSmoothFunctionSpace) : L (nativeSmoothSobolevLinear f) =
      R (nativeSmoothSobolevLinear f) := by
    change TauCeti.W1p.value (nativeH1InwardDilation a (smoothSobolev ⟨f.1,f.2⟩)) =
      nativeUnitBallValueInwardDilation a ha ha1 (TauCeti.W1p.value (smoothSobolev ⟨f.1,f.2⟩))
    rw [nativeH1InwardDilation_smoothSobolev a ha ha1 ⟨f.1,f.2⟩]
    apply Lp.ext
    filter_upwards [value_smoothSobolev_ae (smoothData_inwardDilation ⟨f.1,f.2⟩ a),
      nativeUnitBallValueInwardDilation_apply_ae a ha ha1
        (TauCeti.W1p.value (smoothSobolev ⟨f.1,f.2⟩)),
      (quasiMeasurePreserving_unitBall_inwardDilation a ha ha1).ae_eq_comp
        (value_smoothSobolev_ae ⟨f.1,f.2⟩)] with x hLeft hRight hOriginal
    simpa only [smoothData_inwardDilation,Function.comp_apply] using
      hLeft.trans (hRight.trans hOriginal).symm
  exact denseRange_nativeSmoothSobolevLinear.induction_on u
    (isClosed_eq L.continuous R.continuous) hSmooth

theorem value_nativeH1InwardDilation_ae_innerRepresentative
    (a b : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) (hab : a < b)
    (u : BallH1) (F : R3 → ℝ)
    (hRep : (TauCeti.W1p.value u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) b)] F) :
    (TauCeti.W1p.value (nativeH1InwardDilation a u) : R3 → ℝ)
      =ᵐ[((volume : Measure R3).restrict ballOpens)] (fun x : R3 => F (a • x)) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) ha
  have hMaps : MapsTo (fun x : R3 => a • x) (ballOpens : Set R3) (ball (0 : R3) b) := by
    intro x hx
    have hxNorm : ‖x‖ < 1 := by
      simpa only [coe_ballOpens,B,mem_ball,dist_zero_right] using hx
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos ha0]
    exact (mul_lt_mul_of_pos_left hxNorm ha0).trans (by simpa only [mul_one] using hab)
  have hQ : QuasiMeasurePreserving (fun x : R3 => a • x)
      ((volume : Measure R3).restrict ballOpens)
      ((volume : Measure R3).restrict (ball (0 : R3) b)) :=
    (quasiMeasurePreserving_smul (μ := (volume : Measure R3)) ha0.ne').restrict hMaps
  rw [value_nativeH1InwardDilation_eq_valueInwardDilation a ha ha1 u]
  exact (nativeUnitBallValueInwardDilation_apply_ae a ha ha1 (TauCeti.W1p.value u)).trans
    (hQ.ae_eq_comp hRep)

theorem nativeH1InwardDilation_eq_smoothSobolev_of_innerRepresentative
    (a b : ℝ) (ha : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) (hab : a < b)
    (u : BallH1) (F : R3 → ℝ)
    (hRep : (TauCeti.W1p.value u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) b)] F)
    (w : SmoothData) (hw : EqOn w.1 (fun x : R3 => F (a • x)) (ballOpens : Set R3)) :
    nativeH1InwardDilation a u = smoothSobolev w := by
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  filter_upwards [value_nativeH1InwardDilation_ae_innerRepresentative a b ha ha1 hab u F hRep,
    value_smoothSobolev_ae w,ae_restrict_mem ballOpens.isOpen.measurableSet] with x hU hW hx
  exact hU.trans ((hW.trans (hw hx)).symm)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.quasiMeasurePreserving_unitBall_inwardDilation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_unitBall_value_inwardDilation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_unitBall_value_inwardDilation_toLp_le_four
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeUnitBallValueInwardDilation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeUnitBallValueInwardDilation_apply_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeH1InwardDilation_eq_valueInwardDilation
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_nativeH1InwardDilation_ae_innerRepresentative
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1InwardDilation_eq_smoothSobolev_of_innerRepresentative
