import Calderon.SupportedDriftPrincipalRegularity
import Calderon.CoefficientMultiplier
import Calderon.MetricHessianDivergence

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal InnerProductSpace Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! The only regularity premise is FixedDirichletRegularity. The
mass forcing is an actual L2 multiplier of the same native H1 value. -/

def nativeCoefficientMassL (hcalc : FixedSobolevCalculus) (M : SmoothCoefficientJets 1) :
    BallH1 →L[ℝ] BallSobolev 0 :=
  (coefficientMultiplier hcalc 0 M).comp
    (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2))

lemma nativeCoefficientMassL_value_ae
    (hcalc : FixedSobolevCalculus) (M : SmoothCoefficientJets 1) (u : BallH1) :
    nativeCoefficientMassL hcalc M u =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => coefficientValue 1 M x * TauCeti.W1p.value u x) := by
  change coefficientMultiplier hcalc 0 M (TauCeti.W1p.value u) =ᵐ[_] _
  simpa only [TauCeti.Wkp.value_zero] using
    coefficientMultiplier_value_ae hcalc 0 M (TauCeti.W1p.value u)

lemma norm_nativeCoefficientMassL_le
    (hcalc : FixedSobolevCalculus) (M : SmoothCoefficientJets 1) :
    ‖nativeCoefficientMassL hcalc M‖ ≤
      (sobolevMultiplierBound hcalc 0 * ‖M‖) *
        ‖TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (norm_coefficientMultiplier_le hcalc 0 M) (norm_nonneg _))

lemma energyIntegrand_eq_principal_add_drift_mass
    (A : Matrix (Fin 3) (Fin 3) ℝ) (B : R3) (c : ℝ) (U V : ℝ × R3) :
    TauCeti.PDE.energyIntegrand A B c U V =
      TauCeti.PDE.energyIntegrand A 0 0 U V +
        (inner ℝ B U.2 * V.1 + (c * U.1) * V.1) := by
  simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.driftForm_apply,
    TauCeti.PDE.massForm_apply,inner_zero_left,zero_mul,add_zero]
  ring

lemma nativePrincipal_twoForcing_integral
    (a : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (u : BallH1) (v : BallH1Zero)
    (d m : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    (∫ x in ballOpens,
      TauCeti.PDE.energyIntegrand (a x) 0 0
        (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField (v : BallH1) x) +
        (d x * TauCeti.W1p.value (v : BallH1) x + m x * TauCeti.W1p.value (v : BallH1) x)) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a 0 0 u (v : BallH1) +
        (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v +
          TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) m v) := by
  let P (x : R3) : ℝ := TauCeti.PDE.energyIntegrand (a x) 0 0
    (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField (v : BallH1) x)
  let D (x : R3) : ℝ := d x * TauCeti.W1p.value (v : BallH1) x
  let M (x : R3) : ℝ := m x * TauCeti.W1p.value (v : BallH1) x
  have hp : Integrable P ((volume : Measure R3).restrict ballOpens) :=
    TauCeti.PDE.integrable_energyIntegrand_jetField hcoeff u (v : BallH1)
  have hd : Integrable D ((volume : Measure R3).restrict ballOpens) :=
    (Lp.memLp d).integrable_mul (Lp.memLp (TauCeti.W1p.value (v : BallH1)))
  have hm : Integrable M ((volume : Measure R3).restrict ballOpens) :=
    (Lp.memLp m).integrable_mul (Lp.memLp (TauCeti.W1p.value (v : BallH1)))
  have heP := TauCeti.PDE.energyFormH1_def (mu := (volume : Measure R3))
    (Omega := ballOpens) a 0 0 u (v : BallH1)
  have heD := TauCeti.PDE.dirichletForcing_apply_eq_setIntegral
    (mu := (volume : Measure R3)) (Omega := ballOpens) d v
  have heM := TauCeti.PDE.dirichletForcing_apply_eq_setIntegral
    (mu := (volume : Measure R3)) (Omega := ballOpens) m v
  exact (integral_add hp (hd.add hm)).trans
    ((congrArg (fun t : ℝ => (∫ x in ballOpens, P x) + t) (integral_add hd hm)).trans
      (congrArg₂ (fun x y : ℝ => x+y) heP.symm
        (congrArg₂ (fun x y : ℝ => x+y) heD.symm heM.symm)))

lemma energyFormH1_eq_principal_add_nativeLowerForcing
    (a : MatrixField) (beta : R3 → R3) (c : R3 → ℝ)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (u : BallH1) (v : BallH1Zero)
    (d m : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (hD : d =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => inner ℝ (beta x) (TauCeti.W1p.gradient u x)))
    (hM : m =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => c x * TauCeti.W1p.value u x)) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta c u (v : BallH1) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a 0 0 u (v : BallH1) +
        (TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) d v +
          TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) m v) := by
  have he : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta c u (v : BallH1) =
      ∫ x in ballOpens, TauCeti.PDE.energyIntegrand (a x) 0 0
        (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField (v : BallH1) x) +
          (d x * TauCeti.W1p.value (v : BallH1) x + m x * TauCeti.W1p.value (v : BallH1) x) := by
    rw [TauCeti.PDE.energyFormH1_def]
    apply integral_congr_ae
    filter_upwards [hD,hM] with x hxD hxM
    rw [energyIntegrand_eq_principal_add_drift_mass]
    simp only [TauCeti.PDE.jetField_apply,hxD,hxM]
  exact he.trans (nativePrincipal_twoForcing_integral a hcoeff u v d m)

lemma supportedDriftL_zero_value_ae
    (hcalc : FixedSobolevCalculus) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0) (u : BallH1) :
    supportedDriftL hcalc 0 beta hbeta K hK hz u =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun x => inner ℝ (beta x) (TauCeti.W1p.gradient u x)) := by
  have hzero : TauCeti.Wkp.firstOrder (mu := (volume : Measure R3))
      (Omega := ballOpens) (p := 2) 0 (u : BallSobolev 1) = u := rfl
  have h := supportedDriftL_value_inner_ae hcalc 0 beta hbeta K hK hz u
  rw [hzero] at h
  simpa only [TauCeti.Wkp.value_zero] using h

lemma energyFormH1_eq_supportedDrift_add_massForcing
    (hcalc : FixedSobolevCalculus) (a : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (M : SmoothCoefficientJets 1)
    (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (coefficientValue 1 M) u (v : BallH1) =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        a beta 0 u (v : BallH1) +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (nativeCoefficientMassL hcalc M u) v := by
  have hfull := energyFormH1_eq_principal_add_nativeLowerForcing a beta (coefficientValue 1 M)
    hcoeff u v (supportedDriftL hcalc 0 beta hbeta K hK hz u) (nativeCoefficientMassL hcalc M u)
    (supportedDriftL_zero_value_ae hcalc beta hbeta K hK hz u)
    (nativeCoefficientMassL_value_ae hcalc M u)
  have hsplit := energyFormH1_eq_principal_add_driftForcing hcalc a hcoeff beta hbeta K hK hz u v
  linarith [hfull,hsplit]

lemma supportedDrift_zeroMass_weakSolution_of_mass_weakSolution
    (hcalc : FixedSobolevCalculus) (a : MatrixField)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (M : SmoothCoefficientJets 1)
    (f : BallSobolev 0) (u : BallH1Zero)
    (hu : TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta (coefficientValue 1 M) f u) :
    TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
      a beta 0 (f-nativeCoefficientMassL hcalc M (u : BallH1)) u := by
  intro v
  have hs := energyFormH1_eq_supportedDrift_add_massForcing hcalc a hcoeff
    beta hbeta K hK hz M (u : BallH1) v
  have hf := dirichletForcing_sub_of_native_eq f
    (nativeCoefficientMassL hcalc M (u : BallH1))
    (nativeCoefficientMassL hcalc M (u : BallH1))
    (f-nativeCoefficientMassL hcalc M (u : BallH1)) v rfl rfl
  have hw := hu v
  linarith [hs,hf,hw]

lemma exists_supportedDriftMass_H2_regularity_lift
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (a : MatrixField) (lam Lam : ℝ)
    (hsmooth : ContDiffOn ℝ ∞ a (Metric.closedBall 0 2))
    (hell : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) a lam Lam)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (M : SmoothCoefficientJets 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : BallSobolev 0) (u : BallH1Zero),
      TauCeti.PDE.IsWeakSolutionDirichlet (mu := (volume : Measure R3)) (Omega := ballOpens)
        a beta (coefficientValue 1 M) f u →
      ∃ U : BallSobolev 2,
        TauCeti.Wkp.firstOrder (mu := (volume : Measure R3)) (Omega := ballOpens)
          (p := 2) 1 U = (u : BallH1) ∧
        ‖U‖ ≤ C * (‖u‖ + ‖f-nativeCoefficientMassL hcalc M (u : BallH1)-
          supportedDriftL hcalc 0 beta hbeta K hK hz (u : BallH1)‖) := by
  obtain ⟨C,hC,hregular⟩ := hreg 0 a lam Lam hsmooth hell hcoeff
  refine ⟨C,hC,?_⟩
  intro f u hu
  have hu0 := supportedDrift_zeroMass_weakSolution_of_mass_weakSolution hcalc a hcoeff
    beta hbeta K hK hz M f u hu
  exact exists_supportedDrift_principal_regularity_lift hcalc 0 a hcoeff C hregular
    beta hbeta K hK hz (f-nativeCoefficientMassL hcalc M (u : BallH1)) u
    (u : BallH1) rfl hu0

def nativeAdjointMassValue (C : SmoothCoefficientJets 1) (G : Fin 3 → SmoothCoefficientJets 2) :
    R3 → ℝ := fun x => coefficientValue 1 C x -
      ∑ i : Fin 3, fderiv ℝ (coefficientValue 2 (G i)) x (coordinateVector i)

lemma contDiff_nativeAdjointMassValue
    (C : SmoothCoefficientJets 1) (G : Fin 3 → SmoothCoefficientJets 2) :
    ContDiff ℝ ∞ (nativeAdjointMassValue C G) := by
  apply (contDiff_coefficientValue 1 C).sub
  apply ContDiff.sum
  intro i hi
  exact ((contDiff_coefficientValue 2 (G i)).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma hasCompactSupport_nativeAdjointMassValue
    (C : SmoothCoefficientJets 1) (G : Fin 3 → SmoothCoefficientJets 2) :
    HasCompactSupport (nativeAdjointMassValue C G) := by
  have hs : HasCompactSupport (∑ i : Fin 3,
      (fun x : R3 => fderiv ℝ (coefficientValue 2 (G i)) x (coordinateVector i))) :=
    HasCompactSupport.finset_sum (fun i hi =>
      (hasCompactSupport_coefficientValue 2 (G i)).fderiv_apply ℝ (coordinateVector i))
  have hsub := (hasCompactSupport_coefficientValue 1 C).sub hs
  change HasCompactSupport (nativeAdjointMassValue C G) at hsub
  exact hsub

def nativeAdjointMassCoefficient
    (C : SmoothCoefficientJets 1) (G : Fin 3 → SmoothCoefficientJets 2) : SmoothCoefficientJets 1 :=
  compactCoefficient 1 (nativeAdjointMassValue C G)
    (contDiff_nativeAdjointMassValue C G) (hasCompactSupport_nativeAdjointMassValue C G)

lemma coefficientValue_nativeAdjointMassCoefficient
    (C : SmoothCoefficientJets 1) (G : Fin 3 → SmoothCoefficientJets 2) :
    coefficientValue 1 (nativeAdjointMassCoefficient C G) = nativeAdjointMassValue C G :=
  coefficientValue_compactCoefficient 1 (nativeAdjointMassValue C G)
    (contDiff_nativeAdjointMassValue C G) (hasCompactSupport_nativeAdjointMassValue C G)

lemma nativeAdjointMassValue_eq_mass_sub_divergence
    (C : SmoothCoefficientJets 1) (G : Fin 3 → SmoothCoefficientJets 2) (x : R3) :
    nativeAdjointMassValue C G x = coefficientValue 1 C x -
      ∑ i : Fin 3, (gradient (coefficientValue 2 (G i)) x) i := by
  simp only [nativeAdjointMassValue,MetricVolume.gradient_coordinate]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoefficientMassL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoefficientMassL_value_ae
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.norm_nativeCoefficientMassL_le
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_eq_supportedDrift_add_massForcing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.supportedDrift_zeroMass_weakSolution_of_mass_weakSolution
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_supportedDriftMass_H2_regularity_lift
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeAdjointMassValue
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeAdjointMassValue
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.hasCompactSupport_nativeAdjointMassValue
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeAdjointMassCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_nativeAdjointMassCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeAdjointMassValue_eq_mass_sub_divergence

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyIntegrand_eq_principal_add_drift_mass
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativePrincipal_twoForcing_integral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_eq_principal_add_nativeLowerForcing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.supportedDriftL_zero_value_ae
