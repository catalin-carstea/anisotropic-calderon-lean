import Calderon.NativeCoordinateEnergyCancellation
import Calderon.NativeH2CoordinateAssembly
import Calderon.NativeH2OrthogonalPullbackExistence

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal ContDiff Gradient InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge

variable (hcalc : FixedSobolevCalculus) (k : Fin 3) {M : ℝ} (hM : 0 ≤ M)
  (hm : ∀ x ∈ (ballOpens : Set R3), |(coordinateSmoothDatum k).1 x| ≤ M)
  (hg : ∀ x ∈ (ballOpens : Set R3), ‖gradient (coordinateSmoothDatum k).1 x‖ ≤ M)

def nativeH2CoordinateProductDerivative (j : Fin 3) (U : BallSobolev 2) : BallH1 :=
  TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
    hM hm hg (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 j U)) +
      (if j = k then TauCeti.Wkp.firstOrder 1 U else 0)

lemma nativeH1CoordinateProduct_value_ae (u : BallH1) :
    TauCeti.W1p.value
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)] fun x => x k * TauCeti.W1p.value u x := by
  rw [TauCeti.W1p.contDiffSMulL_apply]
  filter_upwards [TauCeti.W1p.value_contDiffSMul_ae (coordinateSmoothDatum k).2 hM hm hg u]
    with x hx
  exact hx

lemma nativeH1CoordinateProduct_coordinateGradient_ae (j : Fin 3) (u : BallH1) :
    unitBallCoordinateGradientL j
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg u)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => x k * (TauCeti.W1p.gradient u x) j +
        (if j=k then TauCeti.W1p.value u x else 0) := by
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg
  filter_upwards [unitBallCoordinateGradientL_ae j (S u),
    TauCeti.W1p.gradient_contDiffSMul_ae (coordinateSmoothDatum k).2 hM hm hg u]
    with x hx hgrad
  dsimp only [S] at hx
  rw [TauCeti.W1p.contDiffSMulL_apply] at hx
  rw [TauCeti.W1p.contDiffSMulL_apply]
  rw [hx,hgrad]
  simp only [coordinateSmoothDatum,gradient_coordinate_projection,PiLp.add_apply,
    PiLp.smul_apply,smul_eq_mul,PiLp.single_apply]
  by_cases hj : j=k
  · subst j
    simp only [ite_true,mul_one]
  · simp only [hj,Ne.symm hj,ite_false,mul_zero]

lemma nativeH1Value_add_ae (u v : BallH1) :
    TauCeti.W1p.value (u+v) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => TauCeti.W1p.value u x + TauCeti.W1p.value v x := by
  have h := (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)).map_add u v
  simp only [TauCeti.W1p.valueL_apply] at h
  rw [h]
  filter_upwards [Lp.coeFn_add (TauCeti.W1p.value u) (TauCeti.W1p.value v)] with x hx
  simpa only [Pi.add_apply] using hx

lemma nativeH1Value_zero_ae :
    TauCeti.W1p.value (0 : BallH1) =ᵐ[((volume : Measure R3).restrict ballOpens)] fun _ => (0 : ℝ) := by
  have h := (TauCeti.W1p.valueL (mu := (volume : Measure R3)) (Omega := ballOpens) (p := 2)).map_zero
  simp only [TauCeti.W1p.valueL_apply] at h
  rw [h]
  exact Lp.coeFn_zero ℝ 2 ((volume : Measure R3).restrict ballOpens)

lemma nativeH1CoordinateProduct_delta_value_ae (j : Fin 3) (u d : BallH1) :
    TauCeti.W1p.value
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
        hM hm hg d + (if j=k then u else 0)) =ᵐ[((volume : Measure R3).restrict ballOpens)]
      fun x => x k * TauCeti.W1p.value d x + (if j=k then TauCeti.W1p.value u x else 0) := by
  let S : BallH1 →L[ℝ] BallH1 := TauCeti.W1p.contDiffSMulL
    (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2 hM hm hg
  by_cases hj : j=k
  · simp only [hj,ite_true]
    filter_upwards [nativeH1Value_add_ae (S d) u,
      nativeH1CoordinateProduct_value_ae k hM hm hg d] with x ha hp
    rw [ha,hp]
  · simp only [hj,ite_false]
    filter_upwards [nativeH1Value_add_ae (S d) 0,
      nativeH1CoordinateProduct_value_ae k hM hm hg d,nativeH1Value_zero_ae] with x ha hp hz
    rw [ha,hp,hz]

lemma value_coordinateProductH1_of_gradient_value
    (j : Fin 3) (u d : BallH1)
    (hd : TauCeti.W1p.value d = unitBallCoordinateGradientL j u) :
    TauCeti.W1p.value
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
        hM hm hg d + (if j=k then u else 0)) =
    unitBallCoordinateGradientL j
      (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
        hM hm hg u) := by
  apply Lp.ext
  filter_upwards [nativeH1CoordinateProduct_delta_value_ae k hM hm hg j u d,
    nativeH1CoordinateProduct_coordinateGradient_ae k hM hm hg j u,
    unitBallCoordinateGradientL_ae j u] with x hval hprod hgrad
  have hdx : TauCeti.W1p.value d x = unitBallCoordinateGradientL j u x :=
    congrArg (fun f : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens) => f x) hd
  rw [hval,hprod,hdx,hgrad]

lemma value_nativeH2CoordinateProductDerivative (j : Fin 3) (U : BallSobolev 2) :
    TauCeti.W1p.value (nativeH2CoordinateProductDerivative hcalc k hM hm hg j U) =
      unitBallCoordinateGradientL j
        (TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
          hM hm hg (TauCeti.Wkp.firstOrder 1 U)) := by
  apply value_coordinateProductH1_of_gradient_value k hM hm hg j
  exact (TauCeti.Wkp.value_firstOrder 0 _).trans
    (unitBallCoordinateDerivative_eq_coordinateGradient hcalc 1 j U)

include hcalc hM hm hg

lemma exists_nativeH2CoordinateProduct (U : BallSobolev 2) :
    ∃ V : BallSobolev 2, TauCeti.Wkp.firstOrder 1 V =
      TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
        hM hm hg (TauCeti.Wkp.firstOrder 1 U) :=
  exists_nativeH2_of_coordinate_gradient_values _
    (fun j => nativeH2CoordinateProductDerivative hcalc k hM hm hg j U)
    (fun j => value_nativeH2CoordinateProductDerivative hcalc k hM hm hg j U)

def nativeH2CoordinateProduct (U : BallSobolev 2) : BallSobolev 2 :=
  (exists_nativeH2CoordinateProduct hcalc k hM hm hg U).choose

lemma firstOrder_nativeH2CoordinateProduct (U : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 1 (nativeH2CoordinateProduct hcalc k hM hm hg U) =
      TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
        hM hm hg (TauCeti.Wkp.firstOrder 1 U) :=
  (exists_nativeH2CoordinateProduct hcalc k hM hm hg U).choose_spec

lemma value_nativeH2CoordinateProduct_ae (U : BallSobolev 2) :
    TauCeti.Wkp.value 2 (nativeH2CoordinateProduct hcalc k hM hm hg U)
      =ᵐ[((volume : Measure R3).restrict ballOpens)]
        fun x => x k * TauCeti.Wkp.value 2 U x := by
  have h := congrArg TauCeti.W1p.value
    (firstOrder_nativeH2CoordinateProduct hcalc k hM hm hg U)
  rw [TauCeti.Wkp.value_firstOrder] at h
  rw [h]
  rw [TauCeti.W1p.contDiffSMulL_apply]
  filter_upwards [TauCeti.W1p.value_contDiffSMul_ae (coordinateSmoothDatum k).2 hM hm hg
    (TauCeti.Wkp.firstOrder 1 U)] with x hx
  simpa only [coordinateSmoothDatum,smul_eq_mul,TauCeti.Wkp.value_firstOrder] using hx

lemma coordinateDerivative_nativeH2CoordinateProduct (j : Fin 3) (U : BallSobolev 2) :
    TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 j
      (nativeH2CoordinateProduct hcalc k hM hm hg U)) =
    TauCeti.W1p.contDiffSMulL (coordinateSmoothDatum k).1 (coordinateSmoothDatum k).2
      hM hm hg (TauCeti.Wkp.firstOrder 0 (unitBallCoordinateDerivativeL hcalc 1 j U)) +
        (if j=k then TauCeti.Wkp.firstOrder 1 U else 0) := by
  apply TauCeti.W1p.ext_value
  rw [TauCeti.Wkp.value_firstOrder,unitBallCoordinateDerivative_eq_coordinateGradient,
    firstOrder_nativeH2CoordinateProduct]
  exact (value_nativeH2CoordinateProductDerivative hcalc k hM hm hg j U).symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.value_coordinateProductH1_of_gradient_value

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1CoordinateProduct_value_ae

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1CoordinateProduct_coordinateGradient_ae

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1Value_add_ae

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1Value_zero_ae

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.nativeH1CoordinateProduct_delta_value_ae
