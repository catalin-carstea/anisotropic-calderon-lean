import Calderon.NativeInteriorH2ContinuousRepresentative
import Calderon.LocalContinuousWeakDerivativeClassical
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Direct native weak→classical reconstruction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

theorem exists_contDiffOn_nativeSobolev_innerBall
    (hcalc : FixedSobolevCalculus) (n : ℕ) (U : BallSobolev (n+2))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ F : R3 → ℝ, Continuous F ∧ ContDiffOn ℝ n F (ball (0 : R3) a) ∧
      (TauCeti.Wkp.value (n+2) U : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F := by
  induction n with
  | zero =>
    obtain ⟨F, hF, hRep⟩ :=
      exists_continuous_representative_on_innerBall_of_nativeH2 hcalc U a ha ha1
    refine ⟨F, hF, contDiffOn_zero.mpr hF.continuousOn, ?_⟩
    have hAB : ball (0 : R3) a ⊆ (ballOpens : Set R3) := by
      intro x hx
      change dist x (0 : R3) < 1
      exact (show dist x (0 : R3) < a from hx).trans ha1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAB hRep,
      ae_restrict_mem isOpen_ball.measurableSet] with x hx hxA
    exact (hx (ball_subset_closedBall hxA)).symm
  | succ n ih =>
    let V : BallSobolev (n+2) := TauCeti.Wkp.lowerOrder (n+2) U
    obtain ⟨F, hF, hFdiff, hFrep⟩ := ih V
    have hValueEq : TauCeti.Wkp.value (n+1+2) U = TauCeti.Wkp.value (n+2) V :=
      TauCeti.Wkp.value_succ (n+2) U
    have hValue : (TauCeti.Wkp.value (n+1+2) U : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F := by
      filter_upwards [hFrep] with x hx
      exact (congrArg (fun f : BallSobolev 0 => (f : R3 → ℝ) x) hValueEq).trans hx
    let u : BallH1 := TauCeti.Wkp.firstOrder (n+2) U
    have hExist (i : Fin 3) : ∃ G : R3 → ℝ, Continuous G ∧
        ContDiffOn ℝ n G (ball (0 : R3) a) ∧
        (TauCeti.Wkp.value (n+2) (unitBallCoordinateDerivativeL hcalc (n+2) i U) : R3 → ℝ)
          =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] G :=
      ih (unitBallCoordinateDerivativeL hcalc (n+2) i U)
    choose G hGc hGd hGrep using hExist
    have hAB : ball (0 : R3) a ⊆ (ballOpens : Set R3) := by
      intro x hx
      change dist x (0 : R3) < 1
      exact (show dist x (0 : R3) < a from hx).trans ha1
    have hGi (i : Fin 3) : ∀ᵐ x ∂(volume : Measure R3).restrict (ball (0 : R3) a),
        G i x = (TauCeti.W1p.gradient u x) i := by
      filter_upwards [hGrep i, ae_restrict_of_ae_restrict_of_subset hAB
        (unitBallCoordinateDerivativeL_value_ae hcalc (n+2) i U)] with x hx hd
      exact hx.symm.trans hd
    have hAll : ∀ᵐ x ∂(volume : Measure R3).restrict (ball (0 : R3) a),
        ∀ i : Fin 3, G i x = (TauCeti.W1p.gradient u x) i := ae_all_iff.mpr hGi
    let Q : R3 → R3 := fun x => ∑ i : Fin 3, G i x • coordinateVector i
    have hQ : Continuous Q :=
      continuous_finset_sum Finset.univ (fun i _ => (hGc i).smul continuous_const)
    have hQd : ContDiffOn ℝ n Q (ball (0 : R3) a) :=
      ContDiffOn.sum (fun i _ => (hGd i).smul contDiffOn_const)
    have hGrad : (TauCeti.W1p.gradient u : R3 → R3)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] Q := by
      filter_upwards [hAll] with x hx
      have hSum : Q x = ∑ i : Fin 3, (TauCeti.W1p.gradient u x) i • coordinateVector i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun t : ℝ => t • coordinateVector i) (hx i)
      have hBasis : (∑ i : Fin 3, (TauCeti.W1p.gradient u x) i • coordinateVector i) =
          TauCeti.W1p.gradient u x := by
        simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateVector] using
          (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (TauCeti.W1p.gradient u x)
      exact (hSum.trans hBasis).symm
    let Ω : Opens R3 := ⟨ball (0 : R3) a, isOpen_ball⟩
    have hΩB : Ω ≤ ballOpens := hAB
    have hUA : (TauCeti.W1p.value u : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict Ω] F := by
      filter_upwards [hValue] with x hx
      exact (congrArg (fun f : BallSobolev 0 => (f : R3 → ℝ) x)
        (TauCeti.Wkp.value_firstOrder (n+2) U)).trans hx
    have hWeakField : (fun x => innerSL ℝ (TauCeti.W1p.gradient u x))
        =ᵐ[(volume : Measure R3).restrict Ω] (fun x => innerSL ℝ (Q x)) := by
      filter_upwards [hGrad] with x hx
      exact congrArg (innerSL ℝ) hx
    have hWeak := (((TauCeti.W1p.hasWeakFDerivOn u).mono hΩB).congr_ae hUA).congr_ae_deriv hWeakField
    have hFD (x : R3) (hx : x ∈ ball (0 : R3) a) : HasFDerivAt F (innerSL ℝ (Q x)) x :=
      hasFDerivAt_of_continuous_weakFDerivOn Ω F (fun y => innerSL ℝ (Q y)) hF
        ((innerSL ℝ).continuous.comp hQ) hWeak x hx
    have hField : ContDiffOn ℝ n (fun x => innerSL ℝ (Q x)) (ball (0 : R3) a) :=
      (innerSL ℝ).contDiff.comp_contDiffOn hQd
    have hCD : ContDiffOn ℝ ((n : ℕ∞ω)+1) F (ball (0 : R3) a) :=
      (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn isOpen_ball.uniqueDiffOn).mpr
        ⟨by simp, fun x => innerSL ℝ (Q x), hField, fun x hx => (hFD x hx).hasFDerivWithinAt⟩
    refine ⟨F, hF, ?_, hValue⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hCD

theorem exists_contDiffOn_infty_of_nativeAllOrderValues
    (hcalc : FixedSobolevCalculus) (U : (n : ℕ) → BallSobolev (n+2))
    (hValue : ∀ n : ℕ, TauCeti.Wkp.value (n+2) (U n) = TauCeti.Wkp.value 2 (U 0))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ F : R3 → ℝ, Continuous F ∧ ContDiffOn ℝ ∞ F (ball (0 : R3) a) ∧
      (TauCeti.Wkp.value 2 (U 0) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F := by
  obtain ⟨F, hF, hFzero, hFrep⟩ := exists_contDiffOn_nativeSobolev_innerBall hcalc 0 (U 0) a ha ha1
  refine ⟨F, hF, contDiffOn_infty.mpr ?_, hFrep⟩
  intro n
  obtain ⟨G, hG, hGdiff, hGrep⟩ := exists_contDiffOn_nativeSobolev_innerBall hcalc n (U n) a ha ha1
  have hCoherence : (TauCeti.Wkp.value 2 (U 0) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] TauCeti.Wkp.value (n+2) (U n) :=
    Eventually.of_forall (fun x => congrArg (fun f : BallSobolev 0 => (f : R3 → ℝ) x) (hValue n).symm)
  have hEq : EqOn F G (ball (0 : R3) a) :=
    Measure.eqOn_open_of_ae_eq (hFrep.symm.trans (hCoherence.trans hGrep))
      isOpen_ball hF.continuousOn hG.continuousOn
  exact hGdiff.congr (fun x hx => hEq hx)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_contDiffOn_nativeSobolev_innerBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_contDiffOn_infty_of_nativeAllOrderValues
