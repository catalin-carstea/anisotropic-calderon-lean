import Calderon.NativeH3CoefficientConormalTrace
import Calderon.NativePrincipalOperatorOrderCoherence
import Calderon.NativeH2CoefficientFluxGreen
import Calderon.NativeZeroValueTrace

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge SphereHarmonic NativeH3CoefficientConormalTrace NativePolynomialBulkMoments

def nativePrincipalHarmonicConormalDensity
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (r : ℝ) (F : SmoothCoefficientMatrix 3) (E : BallSobolev 3) :
    SphereSobolev (3/2 : ℝ) :=
  (r * sphereSurfaceMass) • nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F
    (strongHarmonicProjectionL 1 (ordinaryPrincipalL hcalc 1 F) E - E)

attribute [local irreducible] nativeThreeHalfCoefficientConormalTraceL ordinaryPrincipalL
  strongHarmonicProjectionL sphereSobolevInclusionL sphereSobolevZeroEquiv ordinaryConormalTraceL

theorem sphereSobolevInclusionL_zero_nativePrincipalHarmonicConormalDensity
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (r : ℝ) (F : SmoothCoefficientMatrix 3) (G : SmoothCoefficientMatrix 2)
    (hFG : ∀ i j, coefficientValue 3 (F i j) = coefficientValue 2 (G i j))
    (E : BallSobolev 3) :
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
      (nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 r F E) =
    sphereSobolevZeroEquiv hO hD ((r * sphereSurfaceMass) •
      (ordinaryConormalTraceL hcalc τ0 G
        (TauCeti.Wkp.lowerOrder 2 (strongHarmonicProjectionL 1 (ordinaryPrincipalL hcalc 1 F) E)) -
       ordinaryConormalTraceL hcalc τ0 G (TauCeti.Wkp.lowerOrder 2 E))) := by
  rw [nativePrincipalHarmonicConormalDensity,map_smul,
    sphereSobolevInclusionL_zero_nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F G hFG,
    ← map_smul]
  apply congrArg (sphereSobolevZeroEquiv hO hD)
  apply congrArg (fun v : SphereL2 => (r * sphereSurfaceMass) • v)
  change ordinaryConormalTraceL hcalc τ0 G
    (TauCeti.Wkp.lowerOrderL 2 (_ - E)) = _
  rw [map_sub,map_sub]
  rfl

theorem nativePrincipalHarmonicConormalDensity_represents_Wronskian
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (r : ℝ) (F : SmoothCoefficientMatrix 3) (G : SmoothCoefficientMatrix 2)
    (hFG : ∀ i j, coefficientValue 3 (F i j) = coefficientValue 2 (G i j))
    (hi : ((ordinaryPrincipalL hcalc 1 F).comp
      (strongDirichletSubmodule 1).toSubmodule.subtypeL).IsInvertible)
    (hSym : ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, (coefficientMatrixField 2 G x).IsSymm)
    (E : BallSobolev 3) (U : BallSobolev 2) (hU : ordinaryPrincipalL hcalc 0 G U = 0) :
    ⟪(sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
        (nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 r F E)),
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)⟫_ℝ =
    r * sphereSurfaceMass *
      (⟪τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 E), ordinaryConormalTraceL hcalc τ0 G U⟫_ℝ -
        ⟪ordinaryConormalTraceL hcalc τ0 G (TauCeti.Wkp.lowerOrder 2 E),
          τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)⟫_ℝ) := by
  let H := strongHarmonicProjectionL 1 (ordinaryPrincipalL hcalc 1 F) E
  let H2 := TauCeti.Wkp.lowerOrder 2 H
  have hH : ordinaryPrincipalL hcalc 0 G H2 = 0 :=
    ordinaryPrincipalL_lowerOrder_strongHarmonicProjectionL_eq_zero hcalc 0 F G hFG hi E
  have hTrace : τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 H2) =
      τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 E) := by
    change strongValueTraceL τ0 1 H = strongValueTraceL τ0 1 E
    exact strongValueTraceL_strongHarmonicProjection τ0 1 (ordinaryPrincipalL hcalc 1 F) E
  have hUH := ordinaryPrincipalL_harmonic_full_test_energy hcalc τ0 G U hU
    (TauCeti.Wkp.firstOrder 1 H2)
  have hHU := ordinaryPrincipalL_harmonic_full_test_energy hcalc τ0 G H2 hH
    (TauCeti.Wkp.firstOrder 1 U)
  have hComm := TauCeti.PDE.energyFormH1_comm_of_isSymm_ae (c := (0 : R3 → ℝ)) hSym
    (TauCeti.Wkp.firstOrder 1 U) (TauCeti.Wkp.firstOrder 1 H2)
  have hPair : sphereSurfaceMass *
      ⟪ordinaryConormalTraceL hcalc τ0 G H2,τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)⟫_ℝ =
    sphereSurfaceMass * ⟪τ0.valueTraceL (TauCeti.Wkp.firstOrder 2 E),ordinaryConormalTraceL hcalc τ0 G U⟫_ℝ := by
    rw [hTrace] at hUH
    rw [hUH,hHU] at hComm
    rw [real_inner_comm] at hComm
    exact hComm.symm
  rw [sphereSobolevInclusionL_zero_nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 r F G hFG,
    LinearIsometryEquiv.symm_apply_apply,real_inner_smul_left,inner_sub_left]
  change (r * sphereSurfaceMass) *
    (⟪ordinaryConormalTraceL hcalc τ0 G H2,τ0.valueTraceL (TauCeti.Wkp.firstOrder 1 U)⟫_ℝ - _) = _
  have algebra (a b c m q : ℝ) (h : m*a=m*c) :
      (q*m)*(a-b)=(q*m)*(c-b) := by
    calc
      _ = q*(m*a-m*b) := by ring
      _ = q*(m*c-m*b) := by rw [h]
      _ = _ := by ring
  exact algebra _ _ _ _ _ hPair


theorem contDiffOn_nativePrincipalHarmonicConormalDensity
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : WithTop ℕ∞}
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (r : V → ℝ) (F : V → SmoothCoefficientMatrix 3)
    (E : V → BallSobolev 3) (s : Set V) (hr : ContDiffOn ℝ n r s)
    (hCoeff : ContDiffOn ℝ n F s) (hE : ContDiffOn ℝ n E s)
    (hi : ∀ p ∈ s, ((ordinaryPrincipalL hcalc 1 (F p)).comp
      (strongDirichletSubmodule 1).toSubmodule.subtypeL).IsInvertible) :
    ContDiffOn ℝ n (fun p => nativePrincipalHarmonicConormalDensity hcalc hF hO hD τ0 (r p) (F p) (E p)) s := by
  have hA : ContDiffOn ℝ n (fun p => ordinaryPrincipalL hcalc 1 (F p)) s := by
    have heq : (fun p => ordinaryCoefficientOperatorL hcalc 1 (F p)) =
        (fun p => ordinaryPrincipalL hcalc 1 (F p)) := funext fun p => by
      unfold ordinaryPrincipalL
      rfl
    rw [← heq]
    exact (ordinaryCoefficientOperatorL hcalc 1).contDiff.comp_contDiffOn hCoeff
  have hP := contDiffOn_strongHarmonicProjectionL 1 (fun p => ordinaryPrincipalL hcalc 1 (F p)) s hA hi
  have hEntry (i j : Fin 3) : ContDiffOn ℝ n (fun p => F p i j) s := by
    let ev1 : SmoothCoefficientMatrix 3 →L[ℝ] (Fin 3 → SmoothCoefficientJets 3) :=
      ContinuousLinearMap.proj i
    let ev2 : (Fin 3 → SmoothCoefficientJets 3) →L[ℝ] SmoothCoefficientJets 3 :=
      ContinuousLinearMap.proj j
    exact (ev2.comp ev1).contDiff.comp_contDiffOn hCoeff
  have hC := contDiffOn_nativeThreeHalfCoefficientConormalTraceL hcalc hF hO hD τ0 F s hEntry
  exact (hr.mul contDiffOn_const).smul (hC.clm_apply ((hP.clm_apply hE).sub hE))

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
