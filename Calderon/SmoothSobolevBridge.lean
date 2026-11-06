import Calderon.SobolevEnergyBridge
import Calderon.InfimumClosure
import TauCeti.Analysis.PDE.DirichletProblem

noncomputable section
open MeasureTheory
open scoped Distributions ENNReal InnerProductSpace Gradient ContDiff

namespace OAI.AnisotropicCalderon.EnergyBridge

abbrev BallH1 := TauCeti.W1p (volume : Measure R3) ballOpens 2
abbrev BallH1Zero := TauCeti.W1p0 (volume : Measure R3) ballOpens 2

/-- Continuity on ambient space is sufficient for the exact bounded-ball L2 embedding. -/
theorem memLp_two_restrict_ball_of_continuous {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [SecondCountableTopology V] {f : R3 → V} (hf : Continuous f) :
    MemLp f 2 ((volume : Measure R3).restrict ballOpens) := by
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hfinite : IsFiniteMeasure ((volume : Measure R3).restrict ballOpens) :=
    ⟨by simpa only [Measure.restrict_apply_univ, coe_ballOpens] using
      ((measure_mono (show B ⊆ Metric.closedBall (0 : R3) 1 from Metric.ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 1).measure_lt_top)⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : R3) 1).bddAbove_image hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hB] with x hx
  exact hC ⟨x, Metric.ball_subset_closedBall hx, rfl⟩

/-- Real globally smooth data, with the original ambient functions retained. -/
abbrev SmoothData := {f : R3 → ℝ // ContDiff ℝ ∞ f}

theorem memLp_smooth_value (f : SmoothData) :
    MemLp f.1 2 ((volume : Measure R3).restrict ballOpens) :=
  memLp_two_restrict_ball_of_continuous f.2.continuous

theorem memLp_smooth_gradient (f : SmoothData) :
    MemLp (gradient f.1) 2 ((volume : Measure R3).restrict ballOpens) :=
  memLp_two_restrict_ball_of_continuous (f.2.gradient_right (m := 0) (by simp)).continuous

private theorem hasWeakFDerivOn_smoothLp (f : SmoothData) :
    TauCeti.HasWeakFDerivOn volume ballOpens ((memLp_smooth_value f).toLp f.1)
      (fun x => innerSL ℝ ((memLp_smooth_gradient f).toLp (gradient f.1) x)) := by
  have hclassical : TauCeti.HasWeakFDerivOn volume ballOpens f.1 (fderiv ℝ f.1) :=
    TauCeti.hasWeakFDerivOn_of_differentiableOn
      (f.2.continuous.locallyIntegrable.locallyIntegrableOn _)
      ((f.2.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn _)
      (fun x _ => (f.2.differentiable (by simp)) x)
  refine (hclassical.congr_ae (Filter.EventuallyEq.symm (MemLp.coeFn_toLp (memLp_smooth_value f)))).congr_ae_deriv ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_smooth_gradient f)] with x hx
  rw [hx]
  ext v
  exact (inner_gradient_left (𝕜 := ℝ) (f := f.1) (x := x) (y := v)).symm

/-- The actual Tau Ceti weak Sobolev jet of every frozen smooth datum. -/
def smoothSobolev (f : SmoothData) : BallH1 :=
  TauCeti.W1p.mk ((memLp_smooth_value f).toLp f.1)
    ((memLp_smooth_gradient f).toLp (gradient f.1)) (hasWeakFDerivOn_smoothLp f)

theorem value_smoothSobolev_ae (f : SmoothData) :
    TauCeti.W1p.value (smoothSobolev f) =ᵐ[(volume : Measure R3).restrict ballOpens] f.1 := by
  unfold smoothSobolev
  change TauCeti.W1p.value (TauCeti.W1p.mk _ _ _) =ᵐ[(volume : Measure R3).restrict ballOpens] f.1
  rw [TauCeti.W1p.value_mk]
  exact MemLp.coeFn_toLp (memLp_smooth_value f)

theorem gradient_smoothSobolev_ae (f : SmoothData) :
    TauCeti.W1p.gradient (smoothSobolev f) =ᵐ[(volume : Measure R3).restrict ballOpens] gradient f.1 := by
  unfold smoothSobolev
  change TauCeti.W1p.gradient (TauCeti.W1p.mk _ _ _) =ᵐ[(volume : Measure R3).restrict ballOpens] gradient f.1
  rw [TauCeti.W1p.gradient_mk]
  exact MemLp.coeFn_toLp (memLp_smooth_gradient f)

theorem jetField_smoothSobolev_ae (f : SmoothData) :
    TauCeti.PDE.jetField (smoothSobolev f) =ᵐ[(volume : Measure R3).restrict ballOpens] energyJet f.1 := by
  filter_upwards [value_smoothSobolev_ae f, gradient_smoothSobolev_ae f] with x hx hy
  simp only [TauCeti.PDE.jetField_apply, energyJet, energyGradient_eq_gradient, hx, hy]

/-- Every full smooth datum has the exact frozen energy in the actual Sobolev form. -/
theorem energy_smooth_eq_energyFormH1 (g : MatrixField) (f : SmoothData) :
    energy g f.1 = TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
      (smoothSobolev f) (smoothSobolev f) := by
  rw [energy_eq_energyFormIntegral]
  unfold TauCeti.PDE.energyFormH1 TauCeti.PDE.energyFormIntegral
  apply integral_congr_ae
  filter_upwards [jetField_smoothSobolev_ae f] with x hx
  simp only [hx, Pi.zero_apply]

theorem smoothSobolev_testFunction (φ : 𝓓(ballOpens, ℝ)) :
    smoothSobolev ⟨φ, φ.contDiff⟩ = testFunctionSobolev φ := by
  apply TauCeti.W1p.ext_value
  apply Lp.ext
  exact (value_smoothSobolev_ae ⟨φ, φ.contDiff⟩).trans
    (by
      change (φ : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict ballOpens]
        TauCeti.W1p.value (TauCeti.W1p.ofTestFunctionₗ volume ballOpens 2 φ)
      rw [TauCeti.W1p.value_ofTestFunctionₗ]
      exact Filter.EventuallyEq.symm (TauCeti.testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ))

/-- Exact value representative, useful for linearity without arbitrary pointwise representatives. -/
theorem value_smoothSobolev (f : SmoothData) :
    TauCeti.W1p.value (smoothSobolev f) = (memLp_smooth_value f).toLp f.1 := by
  unfold smoothSobolev
  change TauCeti.W1p.value (TauCeti.W1p.mk _ _ _) = _
  rw [TauCeti.W1p.value_mk]

/-- The canonical embedding respects affine sums of all frozen globally smooth data. -/
theorem smoothSobolev_add (f h : SmoothData) :
    smoothSobolev ⟨f.1 + h.1, f.2.add h.2⟩ = smoothSobolev f + smoothSobolev h := by
  apply TauCeti.W1p.ext_value
  simp only [← TauCeti.W1p.valueL_apply, map_add]
  simp only [TauCeti.W1p.valueL_apply, value_smoothSobolev]
  exact MemLp.toLp_add (memLp_smooth_value f) (memLp_smooth_value h)

/-- The canonical embedding also respects differences of globally smooth data. -/
theorem smoothSobolev_sub (f h : SmoothData) :
    smoothSobolev ⟨f.1 - h.1, f.2.sub h.2⟩ = smoothSobolev f - smoothSobolev h := by
  apply TauCeti.W1p.ext_value
  simp only [← TauCeti.W1p.valueL_apply, map_sub]
  simp only [TauCeti.W1p.valueL_apply, value_smoothSobolev]
  exact MemLp.toLp_sub (memLp_smooth_value f) (memLp_smooth_value h)

/-- The narrow published-source interface proposed for independent source review.
This definition installs no assumption or axiom; theorems explicitly take a proof parameter. -/
def SmoothBoundaryZeroClosure : Prop :=
  ∀ f : SmoothData, (∀ x : R3, ‖x‖ = 1 → f.1 x = 0) →
    smoothSobolev f ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2

/-- The genuine full frozen zero-exterior functions, embedded in the existing Sobolev space. -/
def smoothZeroSobolev : Set BallH1 :=
  {u | ∃ w : SmoothData, w.1 ∈ smoothZeroExterior ∧ smoothSobolev w = u}

/-- The full frozen perturbation space has exactly the existing H1_0 closure,
conditional only on the displayed standard zero-trace interface. -/
theorem closure_smoothZeroSobolev_eq (hzero : SmoothBoundaryZeroClosure) :
    closure smoothZeroSobolev =
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 : Set BallH1) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (TauCeti.w1p0Submodule volume ballOpens 2).isClosed
    rintro u ⟨w, hw, rfl⟩
    apply hzero w
    intro x hx
    exact hw.2 x hx.ge
  · rw [TauCeti.coe_w1p0Submodule]
    apply closure_mono
    rintro u ⟨φ, rfl⟩
    refine ⟨⟨φ, φ.contDiff⟩, testFunction_mem_smoothZeroExterior φ, ?_⟩
    exact smoothSobolev_testFunction φ

theorem smoothZeroSobolev_nonempty : smoothZeroSobolev.Nonempty := by
  refine ⟨smoothSobolev ⟨0, contDiff_const⟩, ⟨⟨0, contDiff_const⟩, ?_, rfl⟩⟩
  exact ⟨contDiff_const, fun _ _ => rfl⟩

/-- The existing continuous Tau bilinear form gives the actual affine energy functional. -/
def affineSobolevEnergy (g : MatrixField) (f : SmoothData) (v : BallH1) : ℝ :=
  TauCeti.PDE.energyFormH1 (principalCoefficient g) 0 0
    (smoothSobolev f + v) (smoothSobolev f + v)

theorem continuous_affineSobolevEnergy (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens)) :
    Continuous (affineSobolevEnergy g f) := by
  have h : Continuous (fun v : BallH1 => smoothSobolev f + v) := continuous_const.add continuous_id
  let hB := TauCeti.PDE.energyFormH1L (mu := (volume : Measure R3))
    (Omega := ballOpens) hcoeff
  have hc := (hB.continuous.comp h).clm_apply h
  apply hc.congr
  intro v
  exact TauCeti.PDE.energyFormH1L_apply hcoeff (smoothSobolev f + v) (smoothSobolev f + v)

/-- Exact image identity using every smooth zero-exterior competitor, not only test functions. -/
theorem smoothEnergy_image_eq (g : MatrixField) (f : SmoothData) :
    ((fun w => energy g (f.1 + w)) '' smoothZeroExterior) =
      affineSobolevEnergy g f '' smoothZeroSobolev := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨smoothSobolev ⟨w, hw.1⟩, ⟨⟨w, hw.1⟩, hw, rfl⟩, ?_⟩
    unfold affineSobolevEnergy
    rw [← smoothSobolev_add]
    exact (energy_smooth_eq_energyFormH1 g ⟨f.1 + w, f.2.add hw.1⟩).symm
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨w.1, hw, ?_⟩
    unfold affineSobolevEnergy
    rw [← smoothSobolev_add]
    exact energy_smooth_eq_energyFormH1 g ⟨f.1 + w.1, f.2.add w.2⟩

/-- The exact frozen real infimum equals the actual affine H1_0 energy infimum.
All boundedness and standard density obligations remain explicit. -/
theorem minimalEnergy_eq_sInf_affineSobolevEnergy
    (hzero : SmoothBoundaryZeroClosure) (g : MatrixField) (f : SmoothData)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (principalCoefficient g x) 0 0)
      ⊤ ((volume : Measure R3).restrict ballOpens))
    (hbelow : BddBelow (affineSobolevEnergy g f ''
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 : Set BallH1))) :
    minimalEnergy g f.1 = sInf (affineSobolevEnergy g f ''
      (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 : Set BallH1)) := by
  rw [minimalEnergy_eq_sInf_smoothZeroExterior g f.1 f.2, smoothEnergy_image_eq]
  rw [← closure_smoothZeroSobolev_eq hzero] at hbelow ⊢
  exact (sInf_image_closure_eq smoothZeroSobolev_nonempty
    (continuous_affineSobolevEnergy g f hcoeff) hbelow).symm

/-- The constructed classical jet has exactly the source W1_2 graph norm.
This checked identity separates representation from the external zero-trace density parameter. -/
theorem norm_smoothSobolev_sq_eq_graph_integrals (f : SmoothData) :
    ‖smoothSobolev f‖ ^ 2 =
      (∫ x in B, (f.1 x) ^ 2) + (∫ x in B, ‖energyGradient f.1 x‖ ^ 2) := by
  rw [TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
  congr 1
  · rw [← TauCeti.W1p.integral_value_sq_eq_norm_value_sq]
    apply integral_congr_ae
    filter_upwards [value_smoothSobolev_ae f] with x hx
    rw [hx]
  · rw [← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
    apply integral_congr_ae
    filter_upwards [gradient_smoothSobolev_ae f] with x hx
    rw [hx, energyGradient_eq_gradient]

end OAI.AnisotropicCalderon.EnergyBridge

#print axioms OAI.AnisotropicCalderon.EnergyBridge.energy_smooth_eq_energyFormH1
#print axioms OAI.AnisotropicCalderon.EnergyBridge.minimalEnergy_eq_sInf_affineSobolevEnergy

#print axioms OAI.AnisotropicCalderon.EnergyBridge.norm_smoothSobolev_sq_eq_graph_integrals
