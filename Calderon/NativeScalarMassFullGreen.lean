import Calderon.NativeScalarMassPrincipalRegularity
import Calderon.NativeWeightedDriftFluxGreen
import Calderon.NativeContinuousCoefficientOrthogonalEnergy
import Calderon.NativeZeroValueTrace
import Calderon.DirichletForcingInjectivity
import Calderon.NativeSupportedAdjointH2Regularity

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativePolynomialBulkMoments
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-! Actual H1 tests, literal mass density and probability/surface-mass normalization. -/

lemma energyIntegrand_add_mass_apply (A : Matrix (Fin 3) (Fin 3) ℝ) (b : R3) (c : ℝ)
    (U V : ℝ × R3) :
    TauCeti.PDE.energyIntegrand A b c U V =
      TauCeti.PDE.energyIntegrand A b 0 U V + (c*U.1)*V.1 := by
  simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.massForm_apply]
  ring

lemma nativeBaseEnergy_mass_integral (a : MatrixField) (b : R3 → R3)
    (hBase : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1) (m : BallSobolev 0) :
    (∫ x in ballOpens, TauCeti.PDE.energyIntegrand (a x) (b x) 0
      (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)+m x*TauCeti.W1p.value v x
        ∂(volume : Measure R3)) =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b 0 u v +
      ⟪m,TauCeti.W1p.value v⟫_ℝ := by
  have hp := TauCeti.PDE.integrable_energyIntegrand_jetField hBase u v
  have hm := (Lp.memLp m).integrable_mul (Lp.memLp (TauCeti.W1p.value v))
  have he : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b 0 u v =
      ∫ x in ballOpens, TauCeti.PDE.energyIntegrand (a x) (b x) 0
        (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x) ∂(volume : Measure R3) :=
    TauCeti.PDE.energyFormH1_def a b 0 u v
  have hi : ⟪m,TauCeti.W1p.value v⟫_ℝ =
      ∫ x in ballOpens, m x*TauCeti.W1p.value v x ∂(volume : Measure R3) := by
    rw [L2.inner_def]
    exact integral_congr_ae (ae_of_all _ (fun x => Real.inner_apply _ _))
  exact (integral_add hp hm).trans (congrArg₂ (fun x y : ℝ => x+y) he.symm hi.symm)

lemma energyFormH1_add_mass_of_native_density (a : MatrixField) (b : R3 → R3) (c : R3 → ℝ)
    (hBase : MemLp (fun x => TauCeti.PDE.energyIntegrand (a x) (b x) 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) (u v : BallH1) (m : BallSobolev 0)
    (hMass : m =ᵐ[((volume : Measure R3).restrict ballOpens)]
      (fun x => c x*TauCeti.W1p.value u x)) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u v =
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b 0 u v +
        ⟪m,TauCeti.W1p.value v⟫_ℝ := by
  have he : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens) a b c u v =
      ∫ x in ballOpens, TauCeti.PDE.energyIntegrand (a x) (b x) 0
        (TauCeti.PDE.jetField u x) (TauCeti.PDE.jetField v x)+m x*TauCeti.W1p.value v x
          ∂(volume : Measure R3) := by
    rw [TauCeti.PDE.energyFormH1_def]
    apply integral_congr_ae
    filter_upwards [hMass] with x hx
    rw [energyIntegrand_add_mass_apply]
    simp only [TauCeti.PDE.jetField_apply,hx]
  exact he.trans (nativeBaseEnergy_mass_integral a b hBase u v m)

lemma coefficient_energyFormH1_add_nativeMass
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (M : SmoothCoefficientJets 1) (u v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta (coefficientValue 1 M) u v =
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta 0 u v +
        ⟪nativeCoefficientMassL hcalc M u,TauCeti.W1p.value v⟫_ℝ :=
  energyFormH1_add_mass_of_native_density (coefficientMatrixField 2 F) beta (coefficientValue 1 M)
    (memLp_nativeEnergyIntegrand_of_continuous (coefficientMatrixField 2 F) beta 0
      (contDiff_coefficientMatrixField 2 F).continuous hbeta.continuous continuous_const) u v
    (nativeCoefficientMassL hcalc M u) (nativeCoefficientMassL_value_ae hcalc M u)

lemma nativeThreeBulkGreen_composition (E Ebase Ep B : ℝ) (p d m n : BallSobolev 0)
    (hMass : E = Ebase+⟪m,n⟫_ℝ) (hDrift : Ebase = Ep+⟪d,n⟫_ℝ)
    (hPrincipal : Ep = ⟪p,n⟫_ℝ+B) :
    E = ⟪p+d+m,n⟫_ℝ+B := by
  rw [inner_add_left,inner_add_left]
  linarith

attribute [local irreducible] ordinaryPrincipalL supportedDriftL nativeCoefficientMassL

lemma nativeSupportedMass_full_test_energy_Green
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (M : SmoothCoefficientJets 1)
    (U : BallSobolev 2) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta (coefficientValue 1 M) (TauCeti.Wkp.firstOrder 1 U) v =
      ⟪ordinaryPrincipalL hcalc 0 F U+
        supportedDriftL hcalc 0 beta hbeta K hK hz (TauCeti.Wkp.firstOrder 1 U)+
        nativeCoefficientMassL hcalc M (TauCeti.Wkp.firstOrder 1 U),TauCeti.W1p.value v⟫_ℝ +
      sphereSurfaceMass*⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ := by
  have hMass := coefficient_energyFormH1_add_nativeMass hcalc F beta hbeta M (TauCeti.Wkp.firstOrder 1 U) v
  have hDrift := coefficient_energyFormH1_eq_principal_add_supportedDrift_inner
    hcalc F beta hbeta K hK hz (TauCeti.Wkp.firstOrder 1 U) v
  have hp := ordinaryPrincipalL_full_test_energy_Green hcalc τ0 F U v
  have hPrincipal : TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 (TauCeti.Wkp.firstOrder 1 U) v =
      ⟪ordinaryPrincipalL hcalc 0 F U,TauCeti.W1p.value v⟫_ℝ +
        sphereSurfaceMass*⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ := by
    simpa only [TauCeti.Wkp.value_zero] using hp
  exact nativeThreeBulkGreen_composition _ _ _ _ _ _ _ _ hMass hDrift hPrincipal

lemma nativeBulkDensity_zero_of_homogeneous_Green
    (τ0 : UnitBallValueTrace) (q : BallSobolev 0) (Q : SphereL2) (E : BallH1 → ℝ)
    (hGreen : ∀ v : BallH1, E v = ⟪q,TauCeti.W1p.value v⟫_ℝ +
      sphereSurfaceMass*⟪Q,τ0.valueTraceL v⟫_ℝ)
    (hWeak : ∀ v : BallH1Zero, E (v : BallH1) = 0) : q = 0 := by
  apply unitBallDirichletForcing_eq_of_forall q 0
  intro v
  have hg := hGreen (v : BallH1)
  have hb : sphereSurfaceMass*⟪Q,τ0.valueTraceL (v : BallH1)⟫_ℝ = 0 := by
    rw [valueTraceL_zeroDirichlet,_root_.inner_zero_right,mul_zero]
  have hc : E (v : BallH1) = ⟪q,TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
    hg.trans ((congrArg (fun t : ℝ => ⟪q,TauCeti.W1p.value (v : BallH1)⟫_ℝ+t) hb).trans (add_zero _))
  have hq := (TauCeti.PDE.dirichletForcing_apply q v).trans (hc.symm.trans (hWeak v))
  have hz : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) 0 v = 0 := by
    rw [TauCeti.PDE.dirichletForcing_apply,_root_.inner_zero_left]
  exact hq.trans hz.symm

lemma nativeSupportedMass_homogeneous_full_test_energy
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta) (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x, x ∉ K → beta x = 0) (M : SmoothCoefficientJets 1) (U : BallSobolev 2)
    (hWeak : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField 2 F) beta (coefficientValue 1 M)
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) = 0) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta (coefficientValue 1 M) (TauCeti.Wkp.firstOrder 1 U) v =
    sphereSurfaceMass*⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ := by
  let q : BallSobolev 0 := ordinaryPrincipalL hcalc 0 F U+
    supportedDriftL hcalc 0 beta hbeta K hK hz (TauCeti.Wkp.firstOrder 1 U)+
    nativeCoefficientMassL hcalc M (TauCeti.Wkp.firstOrder 1 U)
  have hq := nativeBulkDensity_zero_of_homogeneous_Green τ0 q
    (ordinaryConormalTraceL hcalc τ0 F U)
    (fun w => TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) beta (coefficientValue 1 M) (TauCeti.Wkp.firstOrder 1 U) w)
    (nativeSupportedMass_full_test_energy_Green hcalc τ0 F beta hbeta K hK hz M U) hWeak
  have hg := nativeSupportedMass_full_test_energy_Green hcalc τ0 F beta hbeta K hK hz M U v
  have hb : ⟪q,TauCeti.W1p.value v⟫_ℝ = 0 :=
    (congrArg (fun t : BallSobolev 0 => ⟪t,TauCeti.W1p.value v⟫_ℝ) hq).trans (_root_.inner_zero_left _)
  exact hg.trans ((congrArg (fun t : ℝ => t+
    sphereSurfaceMass*⟪ordinaryConormalTraceL hcalc τ0 F U,τ0.valueTraceL v⟫_ℝ) hb).trans (zero_add _))

lemma nativeSupportedAdjoint_homogeneous_full_test_energy
    (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace) (F : SmoothCoefficientMatrix 2)
    (C : SmoothCoefficientJets 1) (beta : R3 → R3) (hbeta : ContDiff ℝ ∞ beta)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ x, x ∉ K → beta x = 0) (U : BallSobolev 2)
    (hWeak : ∀ v : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
        (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
        (TauCeti.Wkp.firstOrder 1 U) (v : BallH1) = 0) (v : BallH1) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (fun x => (coefficientMatrixField 2 F x)ᵀ) (-beta)
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x)
      (TauCeti.Wkp.firstOrder 1 U) v =
    sphereSurfaceMass*⟪ordinaryConormalTraceL hcalc τ0 (fun i j => F j i) U,τ0.valueTraceL v⟫_ℝ := by
  let M := nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz
  have hm : coefficientValue 1 M =
      (fun x => coefficientValue 1 C x-nativeSupportedDriftDivergence beta x) :=
    coefficientValue_nativeSupportedAdjointMassCoefficient C beta hbeta K hK hz
  have hf : coefficientMatrixField 2 (fun i j => F j i) =
      (fun x => (coefficientMatrixField 2 F x)ᵀ) := rfl
  have huM : ∀ w : BallH1Zero,
      TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMatrixField 2 (fun i j => F j i)) (-beta) (coefficientValue 1 M)
        (TauCeti.Wkp.firstOrder 1 U) (w : BallH1) = 0 := by
    simpa only [hm,hf] using hWeak
  have hg := nativeSupportedMass_homogeneous_full_test_energy hcalc τ0 (fun i j => F j i)
    (-beta) hbeta.neg K hK (nativeSupportedNegativeDrift_zeroOutside beta K hz) M U huM v
  simpa only [hm,hf] using hg

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyIntegrand_add_mass_apply
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeBaseEnergy_mass_integral
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.energyFormH1_add_mass_of_native_density
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficient_energyFormH1_add_nativeMass
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeThreeBulkGreen_composition
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedMass_full_test_energy_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeBulkDensity_zero_of_homogeneous_Green
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedMass_homogeneous_full_test_energy

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeSupportedAdjoint_homogeneous_full_test_energy
