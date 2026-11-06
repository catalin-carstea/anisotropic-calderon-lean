import Calderon.NativeH2CoefficientFluxGreen
import Calderon.SupportedDriftConsistency
import Calderon.ClmInheritedStructureData
import Calderon.InheritedNormedStructureData

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff ENNReal InnerProductSpace Classical Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativePolynomialBulkMoments

/-! Expanded before source in EXPANSION-native-H2-coefficient-flux-Green-v001.json. -/

theorem memLp_unitBall_of_continuous_normed
    {V : Type*} [NormedAddCommGroup V] (f : R3 → V) (hf : Continuous f) :
    MemLp f ⊤ ((volume : Measure R3).restrict ballOpens) := by
  letI : IsFiniteMeasure ((volume : Measure R3).restrict ballOpens) :=
    ⟨by simpa only [Measure.restrict_apply_univ,coe_ballOpens] using
      ((measure_mono (show B ⊆ Metric.closedBall (0 : R3) 1 from Metric.ball_subset_closedBall)).trans_lt
        (isCompact_closedBall (0 : R3) 1).measure_lt_top)⟩
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : R3) 1).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
  exact hC x (Metric.ball_subset_closedBall hx)

lemma memLp_coefficientMatrixEnergyIntegrand_of_smooth (F : SmoothCoefficientMatrix 2) :
    MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) := by
  have hc : Continuous (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) :=
    TauCeti.PDE.Continuous.energyIntegrand (contDiff_coefficientMatrixField 2 F).continuous
      continuous_const continuous_const
  have hbridge :
      Continuous (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) →
      MemLp (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0) ⊤
        ((volume : Measure R3).restrict ballOpens) := by
    have ht := memLp_unitBall_of_continuous_normed
      (fun x : R3 => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F x) 0 0)
    simpa only [real_nontriviallyNormedField_normedField_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,
      normedAddCommGroup_ofSeparation_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] using ht
  exact hbridge hc

lemma coefficient_energyFormH1_eq_principal_add_supportedDrift_inner
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ z, z ∉ K → beta z = 0) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta 0 u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField 2 F) 0 0 u v +
        ⟪supportedDriftL hcalc 0 beta hbeta K hK hz u,TauCeti.W1p.value v⟫_ℝ := by
  let muBall : Measure R3 := (volume : Measure R3).restrict ballOpens
  let d : Lp ℝ 2 muBall := supportedDriftL hcalc 0 beta hbeta K hK hz u
  let principal : R3 → ℝ := fun z =>
    TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F z) (0 : R3) (0 : ℝ)
      (TauCeti.PDE.jetField u z) (TauCeti.PDE.jetField v z)
  let driftPairing : R3 → ℝ := fun z => d z*TauCeti.W1p.value v z
  have hp : Integrable principal muBall :=
    TauCeti.PDE.integrable_energyIntegrand_jetField
      (memLp_coefficientMatrixEnergyIntegrand_of_smooth F) u v
  have hd : Integrable driftPairing muBall :=
    (Lp.memLp d).integrable_mul (Lp.memLp (TauCeti.W1p.value v))
  have hval : d =ᵐ[muBall] (fun z => ⟪beta z,TauCeti.W1p.gradient u z⟫_ℝ) := by
    have h0 : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3))
        (Omega := ballOpens) (p := 2) 0 u = u := TauCeti.Wkp.firstOrder_zero u
    have hv : d =ᵐ[muBall]
        (fun z => ⟪beta z,TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 0 u) z⟫_ℝ) := by
      simpa only [TauCeti.Wkp.value_zero] using
        supportedDriftL_value_inner_ae hcalc 0 beta hbeta K hK hz u
    exact hv.trans (Eventually.of_forall fun z =>
      congrArg (fun w : BallH1 => ⟪beta z,TauCeti.W1p.gradient w z⟫_ℝ) h0)
  have htotal : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta 0 u v = ∫ z, principal z+driftPairing z ∂muBall := by
    rw [TauCeti.PDE.energyFormH1_def]
    apply integral_congr_ae
    filter_upwards [hval] with z hzval
    simp only [principal,driftPairing,Pi.zero_apply,TauCeti.PDE.energyIntegrand_apply,
      TauCeti.PDE.jetField_apply,TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,
      hzval,_root_.inner_zero_left,zero_mul,add_zero]
  have hprincipal : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 u v = ∫ z, principal z ∂muBall :=
    TauCeti.PDE.energyFormH1_def _ _ _ u v
  have hdrift : ⟪d,TauCeti.W1p.value v⟫_ℝ = ∫ z, driftPairing z ∂muBall := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact ae_of_all muBall (fun z => by
      dsimp only [driftPairing]
      rw [Real.inner_apply])
  exact htotal.trans ((integral_add hp hd).trans
    (congrArg₂ (fun x y : ℝ => x+y) hprincipal.symm hdrift.symm))

section
variable (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
  (a : (R3 × ℝ) × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
  (w : (R3 × ℝ) × R3 → ℝ) (hw : ContDiff ℝ ∞ w)
  (b : (R3 × ℝ) × R3 → R3) (hb : ContDiff ℝ ∞ b)
  (K : Set R3) (hK : IsCompact K)
  (hza : ∀ p z, z ∉ K → a (p,z) = 0) (hzw : ∀ p z, z ∉ K → w (p,z) = 0) (L : ℝ)

lemma ordinaryStrongDriftFamily_full_test_energy_Green
    (p : R3 × ℝ) (U : BallSobolev 2) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a (p,z)) (weightedDriftSlice w b L p) 0 (TauCeti.Wkp.firstOrder 1 U) v =
        ⟪TauCeti.Wkp.value 0
          (ordinaryStrongDriftFamily hcalc 0 a ha w hw b hb K hK hza hzw L p U),
            TauCeti.W1p.value v⟫_ℝ +
          sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0
            (commonSupportMatrixFamily 2 a ha K hK hza p) U,τ0.valueTraceL v⟫_ℝ := by
  let F : SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 a ha K hK hza p
  have hsplit := coefficient_energyFormH1_eq_principal_add_supportedDrift_inner hcalc F
    (weightedDriftSlice w b L p) (contDiff_weightedDriftSlice w hw b hb L p)
      K hK (weightedDriftSlice_support w b L p K hzw) (TauCeti.Wkp.firstOrder 1 U) v
  have hP := ordinaryPrincipalL_full_test_energy_Green hcalc τ0 F U v
  have hD := ordinaryWeightedDriftL_value_eq hcalc 0 w hw b hb K hK hzw L p U
  have hA : ⟪TauCeti.Wkp.value 0
      (ordinaryStrongDriftFamily hcalc 0 a ha w hw b hb K hK hza hzw L p U),TauCeti.W1p.value v⟫_ℝ =
      ⟪TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U),TauCeti.W1p.value v⟫_ℝ +
        ⟪TauCeti.Wkp.value 0
          (ordinaryWeightedDriftL hcalc 0 w hw b hb K hK hzw L p U),TauCeti.W1p.value v⟫_ℝ := by
    rw [ordinaryStrongDriftFamily,ContinuousLinearMap.add_apply]
    change ⟪TauCeti.Wkp.valueL 0
      (ordinaryPrincipalL hcalc 0 F U + ordinaryWeightedDriftL hcalc 0 w hw b hb K hK hzw L p U),
        TauCeti.W1p.value v⟫_ℝ = _
    rw [map_add,inner_add_left]
    rfl
  have hfield : coefficientMatrixField 2 F = (fun z => a (p,z)) :=
    coefficientMatrixField_commonSupportMatrixFamily 2 a ha K hK hza p
  rw [hfield] at hsplit hP
  rw [hP,← hD] at hsplit
  change TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun z => a (p,z)) (weightedDriftSlice w b L p) 0 (TauCeti.Wkp.firstOrder 1 U) v =
      ⟪TauCeti.Wkp.value 0 (ordinaryPrincipalL hcalc 0 F U),TauCeti.W1p.value v⟫_ℝ +
        sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ +
        ⟪TauCeti.Wkp.value 0
          (ordinaryWeightedDriftL hcalc 0 w hw b hb K hK hzw L p U),TauCeti.W1p.value v⟫_ℝ at hsplit
  change TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
    (fun z => a (p,z)) (weightedDriftSlice w b L p) 0 (TauCeti.Wkp.firstOrder 1 U) v =
      ⟪TauCeti.Wkp.value 0
        (ordinaryStrongDriftFamily hcalc 0 a ha w hw b hb K hK hza hzw L p U),TauCeti.W1p.value v⟫_ℝ +
        sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ
  linarith

lemma ordinaryStrongDriftFamily_harmonic_full_test_energy
    (p : R3 × ℝ) (U : BallSobolev 2)
    (hU : ordinaryStrongDriftFamily hcalc 0 a ha w hw b hb K hK hza hzw L p U = 0) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun z => a (p,z)) (weightedDriftSlice w b L p) 0 (TauCeti.Wkp.firstOrder 1 U) v =
        sphereSurfaceMass * ⟪ordinaryConormalTraceL hcalc τ0
          (commonSupportMatrixFamily 2 a ha K hK hza p) U,τ0.valueTraceL v⟫_ℝ := by
  rw [ordinaryStrongDriftFamily_full_test_energy_Green hcalc τ0 a ha w hw b hb K hK hza hzw L p U v,hU]
  simp only [TauCeti.Wkp.value_zero,_root_.inner_zero_left,zero_add]

end
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.memLp_coefficientMatrixEnergyIntegrand_of_smooth
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficient_energyFormH1_eq_principal_add_supportedDrift_inner
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryStrongDriftFamily_full_test_energy_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ordinaryStrongDriftFamily_harmonic_full_test_energy
