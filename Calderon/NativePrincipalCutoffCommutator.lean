import Calderon.NativeHighSmoothMultiplierForcing
import Calderon.NativeSmoothMultiplierForcingEnergy
import Calderon.NativeH2SmoothMultiplierDerivative
import Calderon.NativeScalarDirichletForcingProduct
import Calderon.NativeReciprocalGaugeMultipliers
import Calderon.DirichletForcingInjectivity
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Gradient ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open NativeThreeHalfCoefficientMultiplier
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace


def nativePrincipalCutoffCommutatorL (hcalc : FixedSobolevCalculus)
    (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) :
    BallSobolev 2 →L[ℝ] BallSobolev 1 :=
  -nativeHighBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q

theorem nativePrincipalCutoffCommutatorL_value
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3)
    (U : BallSobolev 2) :
    TauCeti.Wkp.value 1 (nativePrincipalCutoffCommutatorL hcalc F Q U) =
      -nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q (TauCeti.Wkp.firstOrder 1 U) := by
  change TauCeti.Wkp.value 1 (-nativeHighBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q U) = _
  calc
    _ = -TauCeti.Wkp.value 1 (nativeHighBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q U) :=
      (TauCeti.Wkp.valueL 1).map_neg _
    _ = _ := congrArg (fun f : BallSobolev 0 => -f)
      (value_nativeHighBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q U)

attribute [local irreducible] ordinaryPrincipalL coefficientMultiplier
  nativePrincipalCutoffCommutatorL nativeHighBulkMultiplierCommutatorForcingL
  nativeBulkMultiplierCommutatorForcingL smoothMultiplierLowerJets coefficientRepackedJets

private theorem unitBallCutoffForcing_add_eval
    (f g : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (f+g) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f v +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) g v := by
  simp only [TauCeti.PDE.dirichletForcing_apply,inner_add_left]

private theorem nativePrincipalCutoff_forcing_product
    (hcalc : FixedSobolevCalculus) (Q : SmoothCoefficientJets 3)
    (f : BallSobolev 0) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 Q) f) v =
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) f
      (nativeCoefficientZeroProductL hcalc (smoothMultiplierLowerJets Q) v) := by
  let vQ : BallH1Zero := nativeCoefficientZeroProductL hcalc (smoothMultiplierLowerJets Q) v
  have hV : TauCeti.W1p.value (vQ : BallH1) =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun z => coefficientValue 3 Q z * TauCeti.W1p.value (v : BallH1) z) := by
    have hVal := congrArg TauCeti.W1p.value
      (nativeCoefficientZeroProductL_coe hcalc (smoothMultiplierLowerJets Q) v)
    rw [hVal]
    simpa only [coefficientValue_smoothMultiplierLowerJets] using
      nativeCoefficientH1ProductL_value_ae hcalc (smoothMultiplierLowerJets Q) (v : BallH1)
  have hF : coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 Q) f =ᵐ[(volume : Measure R3).restrict ballOpens]
      (fun z => coefficientValue 3 Q z * f z) := by
    simpa only [TauCeti.Wkp.value_zero,coefficientValue_repackedJets] using
      coefficientMultiplier_value_ae hcalc 0 (coefficientRepackedJets 3 1 Q) f
  exact dirichletForcing_eq_of_scalar_product_ae f _ v vQ (coefficientValue 3 Q) hF hV

private theorem nativeLowerCutoffH1Product_eq_smul
    (hcalc : FixedSobolevCalculus) (Q : SmoothCoefficientJets 3) (u : BallH1)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ z ∈ (ballOpens : Set R3), |(nativeH2CoefficientSmoothData Q).1 z| ≤ M)
    (hg : ∀ z ∈ (ballOpens : Set R3), ‖gradient (nativeH2CoefficientSmoothData Q).1 z‖ ≤ M) :
    nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q) u =
      TauCeti.W1p.contDiffSMulL (nativeH2CoefficientSmoothData Q).1
        (nativeH2CoefficientSmoothData Q).2 hM hm hg u := by
  have hd : coefficientSmoothData (smoothMultiplierLowerJets Q) = nativeH2CoefficientSmoothData Q := by
    apply Subtype.ext
    exact coefficientValue_smoothMultiplierLowerJets Q
  have hm' : ∀ z ∈ (ballOpens : Set R3),
      |(coefficientSmoothData (smoothMultiplierLowerJets Q)).1 z| ≤ M := by
    simpa only [hd] using hm
  have hg' : ∀ z ∈ (ballOpens : Set R3),
      ‖gradient (coefficientSmoothData (smoothMultiplierLowerJets Q)).1 z‖ ≤ M := by
    simpa only [hd] using hg
  have h := nativeCoefficientH1ProductL_eq_contDiffSMulL hcalc (smoothMultiplierLowerJets Q) hM hm' hg' u
  simpa only [hd] using h


private theorem nativePrincipalCutoff_energy_difference
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3)
    (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0
      (nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q) u) (v : BallH1) -
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) 0 0 u
      (nativeCoefficientZeroProductL hcalc (smoothMultiplierLowerJets Q) v : BallH1Zero) =
    -⟪nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q u,
      TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
  let LQ : SmoothCoefficientJets 2 := smoothMultiplierLowerJets Q
  let m : SmoothData := nativeH2CoefficientSmoothData Q
  let S : BallH1 →L[ℝ] BallH1 := nativeCoefficientH1ProductL hcalc LQ
  let E : BallH1 → BallH1 → ℝ := TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3))
    (Omega := ballOpens) (coefficientMatrixField 2 F) 0 0
  let M : ℝ := Classical.choose (exists_smooth_ball_multiplier_bound m)
  have hM : 0 ≤ M := (Classical.choose_spec (exists_smooth_ball_multiplier_bound m)).1
  have hm : ∀ z ∈ (ballOpens : Set R3), |m.1 z| ≤ M :=
    (Classical.choose_spec (exists_smooth_ball_multiplier_bound m)).2.1
  have hg : ∀ z ∈ (ballOpens : Set R3), ‖gradient m.1 z‖ ≤ M :=
    (Classical.choose_spec (exists_smooth_ball_multiplier_bound m)).2.2
  have hRaw := nativeEnergy_smooth_multiplier_difference_integral
    (coefficientMatrixField 2 F) 0 0 (memLp_coefficientMatrixEnergyIntegrand_of_smooth F)
    m hM hm hg u (v : BallH1)
  have hSu : S u = TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg u :=
    nativeLowerCutoffH1Product_eq_smul hcalc Q u hM hm hg
  have hSv : S (v : BallH1) = TauCeti.W1p.contDiffSMulL m.1 m.2 hM hm hg (v : BallH1) :=
    nativeLowerCutoffH1Product_eq_smul hcalc Q (v : BallH1) hM hm hg
  have hDiff : E (S u) (v : BallH1)-E u (S (v : BallH1)) =
      nativeSmoothMultiplierEnergyResidual (coefficientMatrixField 2 F) 0 0 m u (v : BallH1) :=
    (congrArg₂ (fun x y : ℝ => x-y)
      (congrArg (fun w : BallH1 => E w (v : BallH1)) hSu)
      (congrArg (fun w : BallH1 => E u w) hSv)).trans hRaw
  have hZeroDrift : nativeSmoothDriftField (fun _ : Fin 3 => (0 : SmoothCoefficientJets 1)) = 0 := by
    funext x
    ext i
    rw [nativeSmoothDriftField_coordinate]
    rfl
  have hLink := nativeBulkMultiplierEnergyResidual_eq_neg_forcing hcalc F (fun _ => 0) Q u v
  rw [hZeroDrift] at hLink
  have hVQ : (nativeCoefficientZeroProductL hcalc LQ v : BallH1) = S (v : BallH1) :=
    nativeCoefficientZeroProductL_coe hcalc LQ v
  exact (congrArg (fun w : BallH1 => E (S u) (v : BallH1)-E u w) hVQ).trans (hDiff.trans hLink)

private theorem nativePrincipalCutoff_test_evaluation
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3)
    (U : BallSobolev 2) (v : BallH1Zero) :
    TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (ordinaryPrincipalL hcalc 0 F (coefficientMultiplier hcalc 2 Q U)) v =
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
        (coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 Q) (ordinaryPrincipalL hcalc 0 F U)) v +
      TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (TauCeti.Wkp.value 1 (nativePrincipalCutoffCommutatorL hcalc F Q U)) v := by
  let u : BallH1 := TauCeti.Wkp.firstOrder 1 U
  let S : BallH1 →L[ℝ] BallH1 := nativeCoefficientH1ProductL hcalc (smoothMultiplierLowerJets Q)
  let vQ : BallH1Zero := nativeCoefficientZeroProductL hcalc (smoothMultiplierLowerJets Q) v
  let E : BallH1 → BallH1 → ℝ := TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3))
    (Omega := ballOpens) (coefficientMatrixField 2 F) 0 0
  have hFirst : TauCeti.Wkp.firstOrder 1 (coefficientMultiplier hcalc 2 Q U) = S u :=
    firstOrder_H2SmoothMultiplier_eq_H1Product hcalc Q U
  have hPQUraw : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 F (coefficientMultiplier hcalc 2 Q U)) v =
      E (TauCeti.Wkp.firstOrder 1 (coefficientMultiplier hcalc 2 Q U)) (v : BallH1) :=
    ordinaryPrincipalL_zero_forcing_energy hcalc F (coefficientMultiplier hcalc 2 Q U) v
  have hPQU : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 F (coefficientMultiplier hcalc 2 Q U)) v = E (S u) (v : BallH1) :=
    hPQUraw.trans (congrArg (fun w : BallH1 => E w (v : BallH1)) hFirst)
  have hPU : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (ordinaryPrincipalL hcalc 0 F U) vQ = E u (vQ : BallH1) :=
    ordinaryPrincipalL_zero_forcing_energy hcalc F U vQ
  have hForcing := nativePrincipalCutoff_forcing_product hcalc Q (ordinaryPrincipalL hcalc 0 F U) v
  have hDiff : E (S u) (v : BallH1)-E u (vQ : BallH1) =
      -⟪nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q u,TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
    nativePrincipalCutoff_energy_difference hcalc F Q u v
  have hVal := nativePrincipalCutoffCommutatorL_value hcalc F Q U
  have hB : ⟪TauCeti.Wkp.value 1 (nativePrincipalCutoffCommutatorL hcalc F Q U),TauCeti.W1p.value (v : BallH1)⟫_ℝ =
      -⟪nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q u,TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
    (congrArg (fun f : BallSobolev 0 => ⟪f,TauCeti.W1p.value (v : BallH1)⟫_ℝ) hVal).trans (inner_neg_left _ _)
  have hBforcing : TauCeti.PDE.dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens)
      (TauCeti.Wkp.value 1 (nativePrincipalCutoffCommutatorL hcalc F Q U)) v =
      -⟪nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q u,TauCeti.W1p.value (v : BallH1)⟫_ℝ :=
    (TauCeti.PDE.dirichletForcing_apply _ _).trans hB
  calc
    _ = E (S u) (v : BallH1) := hPQU
    _ = E u (vQ : BallH1) + (-⟪nativeBulkMultiplierCommutatorForcingL hcalc F (fun _ => 0) Q u,
        TauCeti.W1p.value (v : BallH1)⟫_ℝ) := by
      calc
        _ = (E (S u) (v : BallH1)-E u (vQ : BallH1))+E u (vQ : BallH1) := (sub_add_cancel _ _).symm
        _ = _ := congrArg (fun r : ℝ => r+E u (vQ : BallH1)) hDiff
        _ = _ := add_comm _ _
    _ = _ := congrArg₂ (fun x y : ℝ => x+y) (hForcing.trans hPU).symm hBforcing.symm

theorem ordinaryPrincipalL_smooth_cutoff_commutator
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3)
    (U : BallSobolev 2) :
    ordinaryPrincipalL hcalc 0 F (coefficientMultiplier hcalc 2 Q U) =
      coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 Q) (ordinaryPrincipalL hcalc 0 F U) +
        TauCeti.Wkp.value 1 (nativePrincipalCutoffCommutatorL hcalc F Q U) := by
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  have hScalar := nativePrincipalCutoff_test_evaluation hcalc F Q U v
  have hAdd := unitBallCutoffForcing_add_eval
    (coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 Q) (ordinaryPrincipalL hcalc 0 F U))
    (TauCeti.Wkp.value 1 (nativePrincipalCutoffCommutatorL hcalc F Q U)) v
  exact hScalar.trans hAdd.symm

theorem nativeH2Cutoff_mem_strongDirichletSubmodule
    (hcalc : FixedSobolevCalculus) (Q : SmoothCoefficientJets 3) (U : StrongDirichletSpace 0) :
    coefficientMultiplier hcalc 2 Q (U : BallSobolev 2) ∈ strongDirichletSubmodule 0 := by
  apply (mem_strongDirichletSubmodule 0 _).mpr
  rw [firstOrder_H2SmoothMultiplier_eq_H1Product hcalc Q (U : BallSobolev 2)]
  exact nativeCoefficientH1ProductL_mem_zero hcalc (smoothMultiplierLowerJets Q)
    (strongDirichletProjectionL 0 U)

theorem ordinaryPrincipalL_lowerOrder_three
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (G : SmoothCoefficientMatrix 3)
    (hFG : coefficientMatrixField 2 F = coefficientMatrixField 3 G) (Z : BallSobolev 3) :
    ordinaryPrincipalL hcalc 0 F (TauCeti.Wkp.lowerOrder 2 Z) =
      TauCeti.Wkp.value 1 (ordinaryPrincipalL hcalc 1 G Z) := by
  apply unitBallDirichletForcing_eq_of_forall
  intro v
  have hLow := ordinaryPrincipalL_energy hcalc 0 F (TauCeti.Wkp.lowerOrder 2 Z) v
  have hHigh := ordinaryPrincipalL_energy hcalc 1 G Z v
  simp only [TauCeti.Wkp.value_zero] at hLow
  have hFirst : TauCeti.Wkp.firstOrder 1 (TauCeti.Wkp.lowerOrder 2 Z) = TauCeti.Wkp.firstOrder 2 Z :=
    (TauCeti.Wkp.firstOrder_succ 1 Z).symm
  rw [hLow,hHigh,hFG,hFirst]

def nativeStrongDirichletLowerThree (Z : StrongDirichletSpace 1) : StrongDirichletSpace 0 :=
  ⟨TauCeti.Wkp.lowerOrder 2 (Z : BallSobolev 3), by
    change TauCeti.Wkp.firstOrder 1 (TauCeti.Wkp.lowerOrder 2 (Z : BallSobolev 3)) ∈
      TauCeti.w1p0Submodule volume ballOpens 2
    rw [← TauCeti.Wkp.firstOrder_succ 1 (Z : BallSobolev 3)]
    exact Z.property⟩

theorem nativePrincipal_inverse_cutoff_gain_coherence
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2) (G : SmoothCoefficientMatrix 3)
    (hFG : coefficientMatrixField 2 F = coefficientMatrixField 3 G) (Q : SmoothCoefficientJets 3)
    (hLow : (strongDirichletOperator hcalc 0 F).IsInvertible)
    (hHigh : (strongDirichletOperator hcalc 1 G).IsInvertible)
    (f : BallSobolev 0)
    (hCut : coefficientMultiplier hcalc 0 (coefficientRepackedJets 3 1 Q) f = 0) :
    TauCeti.Wkp.lowerOrder 2
      ((strongDirichletOperator hcalc 1 G).inverse
        (nativePrincipalCutoffCommutatorL hcalc F Q
          ((strongDirichletOperator hcalc 0 F).inverse f : BallSobolev 2)) : BallSobolev 3) =
      coefficientMultiplier hcalc 2 Q
        ((strongDirichletOperator hcalc 0 F).inverse f : BallSobolev 2) := by
  let A0 := strongDirichletOperator hcalc 0 F
  let A1 := strongDirichletOperator hcalc 1 G
  let U : StrongDirichletSpace 0 := A0.inverse f
  let Z : StrongDirichletSpace 1 := A1.inverse (nativePrincipalCutoffCommutatorL hcalc F Q (U : BallSobolev 2))
  let V : StrongDirichletSpace 0 :=
    ⟨coefficientMultiplier hcalc 2 Q (U : BallSobolev 2),nativeH2Cutoff_mem_strongDirichletSubmodule hcalc Q U⟩
  have hRestr0 (X : StrongDirichletSpace 0) : ordinaryPrincipalL hcalc 0 F (X : BallSobolev 2) = A0 X :=
    congrArg (fun T : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => T X) (ordinaryPrincipalL_restriction hcalc 0 F)
  have hRestr1 (X : StrongDirichletSpace 1) : ordinaryPrincipalL hcalc 1 G (X : BallSobolev 3) = A1 X :=
    congrArg (fun T : StrongDirichletSpace 1 →L[ℝ] BallSobolev 1 => T X) (ordinaryPrincipalL_restriction hcalc 1 G)
  have hU : ordinaryPrincipalL hcalc 0 F (U : BallSobolev 2) = f :=
    (hRestr0 U).trans (hLow.self_apply_inverse f)
  have hV : A0 V = TauCeti.Wkp.value 1 (nativePrincipalCutoffCommutatorL hcalc F Q (U : BallSobolev 2)) := by
    rw [← hRestr0 V]
    change ordinaryPrincipalL hcalc 0 F (coefficientMultiplier hcalc 2 Q (U : BallSobolev 2)) = _
    rw [ordinaryPrincipalL_smooth_cutoff_commutator,hU,hCut,zero_add]
  have hZ : ordinaryPrincipalL hcalc 1 G (Z : BallSobolev 3) =
      nativePrincipalCutoffCommutatorL hcalc F Q (U : BallSobolev 2) :=
    (hRestr1 Z).trans (hHigh.self_apply_inverse _)
  have hZLow : A0 (nativeStrongDirichletLowerThree Z) =
      TauCeti.Wkp.value 1 (nativePrincipalCutoffCommutatorL hcalc F Q (U : BallSobolev 2)) := by
    rw [← hRestr0 (nativeStrongDirichletLowerThree Z)]
    change ordinaryPrincipalL hcalc 0 F (TauCeti.Wkp.lowerOrder 2 (Z : BallSobolev 3)) = _
    rw [ordinaryPrincipalL_lowerOrder_three hcalc F G hFG,hZ]
  have hEqual := hLow.injective (hZLow.trans hV.symm)
  exact congrArg (fun X : StrongDirichletSpace 0 => (X : BallSobolev 2)) hEqual

end OAI.AnisotropicCalderon.ConnectionError
