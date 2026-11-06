import Calderon.NativeCoordinateCommutatorForcing
import Calderon.NativeCoordinateEnergyCancellation
import Calderon.NativeSmoothCoefficientFullEnergy

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal InnerProductSpace Gradient
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

/-! Upfront expansion: EXPANSION-native-coordinate-forcing-energy-joint-v001.md. -/

theorem energyIntegrand_coordinate_jet_left
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : R3) (c : ℝ) (k : Fin 3) (V : ℝ × R3) :
    TauCeti.PDE.energyIntegrand A b c ((0 : ℝ),EuclideanSpace.single k 1) V =
      (∑ i : Fin 3, V.2 i * A i k) + b k * V.1 := by
  simp [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.matrixBilinearForm_apply,
    TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,Matrix.mulVec,dotProduct,
    PiLp.single_apply,EuclideanSpace.inner_single_right]

theorem energyIntegrand_coordinate_jet_right
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : R3) (c : ℝ) (k : Fin 3) (U : ℝ × R3) :
    TauCeti.PDE.energyIntegrand A b c U ((0 : ℝ),EuclideanSpace.single k 1) =
      ∑ j : Fin 3, A k j * U.2 j := by
  simp [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.matrixBilinearForm_apply,
    TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,Matrix.mulVec,dotProduct,
    PiLp.single_apply]

theorem energyIntegrand_coordinate_jet_residual
    (A : Matrix (Fin 3) (Fin 3) ℝ) (b : R3) (c : ℝ) (k : Fin 3) (U V : ℝ × R3) :
    U.1 * TauCeti.PDE.energyIntegrand A b c ((0 : ℝ),EuclideanSpace.single k 1) V -
      V.1 * TauCeti.PDE.energyIntegrand A b c U ((0 : ℝ),EuclideanSpace.single k 1) =
      (∑ i : Fin 3, V.2 i * (A i k * U.1)) -
      (∑ j : Fin 3, V.1 * (A k j * U.2 j)) + V.1 * (b k * U.1) := by
  rw [energyIntegrand_coordinate_jet_left,energyIntegrand_coordinate_jet_right,mul_add,
    Finset.mul_sum,Finset.mul_sum]
  have hc : (∑ i : Fin 3, U.1 * (V.2 i * A i k)) =
      ∑ i : Fin 3, V.2 i * (A i k * U.1) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hc]
  ring

theorem nativeL2_integral_finite_inner_sub_add
    (C D R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (d V : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    (∫ x in ballOpens, (∑ i : Fin 3, ⟪C i x,D i x⟫_ℝ) -
      (∑ j : Fin 3, ⟪R j x,V x⟫_ℝ) + ⟪d x,V x⟫_ℝ) =
      (∑ i : Fin 3, ⟪C i,D i⟫_ℝ) - (∑ j : Fin 3, ⟪R j,V⟫_ℝ) + ⟪d,V⟫_ℝ := by
  let fc (i : Fin 3) (x : R3) := ⟪C i x,D i x⟫_ℝ
  let fr (j : Fin 3) (x : R3) := ⟪R j x,V x⟫_ℝ
  let fd (x : R3) := ⟪d x,V x⟫_ℝ
  have hic (i : Fin 3) : Integrable (fc i) ((volume : Measure R3).restrict ballOpens) :=
    L2.integrable_inner (𝕜 := ℝ) (C i) (D i)
  have hir (j : Fin 3) : Integrable (fr j) ((volume : Measure R3).restrict ballOpens) :=
    L2.integrable_inner (𝕜 := ℝ) (R j) V
  have hid : Integrable fd ((volume : Measure R3).restrict ballOpens) :=
    L2.integrable_inner (𝕜 := ℝ) d V
  have hsumC := integrable_finsetSum Finset.univ (fun i _ => hic i)
  have hsumR := integrable_finsetSum Finset.univ (fun j _ => hir j)
  have hadd := integral_add (hsumC.sub hsumR) hid
  have hsub := integral_sub hsumC hsumR
  simp only [Pi.sub_apply,Pi.add_apply] at hadd hsub
  change (∫ x in ballOpens, (∑ i : Fin 3, fc i x) - (∑ j : Fin 3, fr j x) + fd x) = _
  rw [hadd,hsub,integral_finsetSum Finset.univ (fun i _ => hic i),
    integral_finsetSum Finset.univ (fun j _ => hir j)]
  rfl

theorem nativeCoordinateForcing_residual_integral
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (G : Fin 3 → SmoothCoefficientJets 1) (k : Fin 3) (u : BallH1) (v : BallH1Zero) :
    let C : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun i => TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (F i k) u)
    let R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun j => coefficientMultiplier hcalc 0 (coefficientFirstJets (F k j)) (unitBallCoordinateGradientL j u)
    let d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      coefficientMultiplier hcalc 0 (G k) (TauCeti.W1p.value u)
    let V : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := TauCeti.W1p.value (v : BallH1)
    let D : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
      fun i => unitBallCoordinateGradientL i (v : BallH1)
    let fc (i : Fin 3) (x : R3) := ⟪C i x,D i x⟫_ℝ
    let fr (j : Fin 3) (x : R3) := ⟪R j x,V x⟫_ℝ
    let fd (x : R3) := ⟪d x,V x⟫_ℝ
    (∫ x in ballOpens,
        TauCeti.W1p.value u x * TauCeti.PDE.energyIntegrand
          (coefficientMatrixField 2 F x) (nativeSmoothDriftField G x) 0
          ((0 : ℝ),EuclideanSpace.single k 1) (TauCeti.PDE.jetField (v : BallH1) x) -
        TauCeti.W1p.value (v : BallH1) x * TauCeti.PDE.energyIntegrand
          (coefficientMatrixField 2 F x) (nativeSmoothDriftField G x) 0
          (TauCeti.PDE.jetField u x) ((0 : ℝ),EuclideanSpace.single k 1)) =
        ∫ x in ballOpens, (∑ i : Fin 3, fc i x) - (∑ j : Fin 3, fr j x) + fd x := by
  let C : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (F i k) u)
  let R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun j => coefficientMultiplier hcalc 0 (coefficientFirstJets (F k j)) (unitBallCoordinateGradientL j u)
  let d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    coefficientMultiplier hcalc 0 (G k) (TauCeti.W1p.value u)
  let V : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := TauCeti.W1p.value (v : BallH1)
  let D : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => unitBallCoordinateGradientL i (v : BallH1)
  let fc (i : Fin 3) (x : R3) := ⟪C i x,D i x⟫_ℝ
  let fr (j : Fin 3) (x : R3) := ⟪R j x,V x⟫_ℝ
  let fd (x : R3) := ⟪d x,V x⟫_ℝ
  have hc : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      C i x = coefficientValue 2 (F i k) x * TauCeti.W1p.value u x :=
    ae_all_iff.mpr fun i => nativeCoefficientH1ProductL_value_ae hcalc (F i k) u
  have hr : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ j : Fin 3,
      R j x = coefficientValue 2 (F k j) x * (TauCeti.W1p.gradient u x) j :=
    ae_all_iff.mpr fun j => nativeCoordinateCommutatorForcing_row_ae hcalc F k j u
  have hd := nativeCoordinateCommutatorForcing_drift_ae hcalc G k u
  have hD : ∀ᵐ x ∂((volume : Measure R3).restrict ballOpens), ∀ i : Fin 3,
      D i x = (TauCeti.W1p.gradient (v : BallH1) x) i :=
    ae_all_iff.mpr fun i => unitBallCoordinateGradientL_ae i (v : BallH1)
  apply integral_congr_ae
  filter_upwards [hc,hr,hd,hD] with x hcx hrx hdx hDx
  change (TauCeti.PDE.jetField u x).1 * _ - (TauCeti.PDE.jetField (v : BallH1) x).1 * _ =
    (∑ i : Fin 3, ⟪C i x,D i x⟫_ℝ) - (∑ j : Fin 3, ⟪R j x,V x⟫_ℝ) + ⟪d x,V x⟫_ℝ
  rw [energyIntegrand_coordinate_jet_residual]
  simp only [TauCeti.PDE.jetField_apply,coefficientMatrixField,nativeSmoothDriftField_coordinate,
    fc,fr,fd,RCLike.inner_apply,conj_trivial]
  simp only [hcx,hrx,hDx]
  change _ = _ + TauCeti.W1p.value (v : BallH1) x * d x
  rw [hdx]

theorem nativeEnergy_coordinate_product_difference_forcing
    (hcalc : FixedSobolevCalculus) (F : SmoothCoefficientMatrix 2)
    (G : Fin 3 → SmoothCoefficientJets 1)
    (hcoeff : MemLp (fun x => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 F x) (nativeSmoothDriftField G x) 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
    (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)
    (u : BallH1) (v : BallH1Zero) :
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) (nativeSmoothDriftField G) 0
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg u)
      (v : BallH1) -
    TauCeti.PDE.energyFormH1 (mu := (volume : Measure R3)) (Omega := ballOpens)
      (coefficientMatrixField 2 F) (nativeSmoothDriftField G) 0 u
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg (v : BallH1)) =
    -⟪nativeCoordinateCommutatorForcingL hcalc F G k u,TauCeti.W1p.value (v : BallH1)⟫_ℝ := by
  let C : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => TauCeti.W1p.value (nativeCoefficientH1ProductL hcalc (F i k) u)
  let R : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun j => coefficientMultiplier hcalc 0 (coefficientFirstJets (F k j)) (unitBallCoordinateGradientL j u)
  let d : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    coefficientMultiplier hcalc 0 (G k) (TauCeti.W1p.value u)
  let V : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) := TauCeti.W1p.value (v : BallH1)
  let D : Fin 3 → Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) :=
    fun i => unitBallCoordinateGradientL i (v : BallH1)
  rw [nativeEnergy_coordinate_product_difference_integral
    (coefficientMatrixField 2 F) (nativeSmoothDriftField G) 0 hcoeff k hM hm hg u (v : BallH1)]
  simp only [Pi.zero_apply]
  rw [nativeCoordinateForcing_residual_integral hcalc F G k u v]
  rw [nativeL2_integral_finite_inner_sub_add]
  have hQ := nativeCoordinateCommutatorForcingL_zero_test hcalc F G k u v
  change ⟪nativeCoordinateCommutatorForcingL hcalc F G k u,V⟫_ℝ =
    -(∑ i : Fin 3, ⟪C i,D i⟫_ℝ) + (∑ j : Fin 3, ⟪R j,V⟫_ℝ) - ⟪d,V⟫_ℝ at hQ
  linarith

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeL2_integral_finite_inner_sub_add

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeCoordinateForcing_residual_integral
