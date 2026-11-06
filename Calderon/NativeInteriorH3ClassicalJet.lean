import Calderon.NativeInteriorH2ContinuousRepresentative
import Calderon.LocalContinuousWeakDerivativeClassical

/-! Native H3 yields an actual local continuous classical first jet; no C∞ claim. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal ContDiff InnerProductSpace Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

theorem exists_continuous_nativeH3_valueGradient_on_innerBall
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 3)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ (F : R3 → ℝ) (Q : R3 → R3), Continuous F ∧ Continuous Q ∧
      ((TauCeti.Wkp.value 3 U : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F) ∧
      ((TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 2 U) : R3 → R3)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] Q) ∧
      TauCeti.HasWeakFDerivOn (volume : Measure R3) ⟨ball (0 : R3) a, isOpen_ball⟩
        F (fun x => innerSL ℝ (Q x)) := by
  let Ω : Opens R3 := ⟨ball (0 : R3) a, isOpen_ball⟩
  have hΩB : Ω ≤ ballOpens := by
    intro x hx
    change dist x (0 : R3) < 1
    have hx' : dist x (0 : R3) < a := hx
    exact hx'.trans ha1
  have hAB : (ball (0 : R3) a) ⊆ (ballOpens : Set R3) := hΩB
  obtain ⟨F, hF, hFrep⟩ := exists_continuous_representative_on_innerBall_of_nativeH2
    hcalc (TauCeti.Wkp.lowerOrder 2 U) a ha ha1
  have hFA : (TauCeti.Wkp.value 3 U : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAB hFrep,
      ae_restrict_mem isOpen_ball.measurableSet] with x hx hxA
    have hxC : x ∈ closedBall (0 : R3) a := ball_subset_closedBall hxA
    exact (congrArg (fun f : BallSobolev 0 => (f : R3 → ℝ) x) (TauCeti.Wkp.value_succ 2 U)).trans (hx hxC).symm
  have hExist (i : Fin 3) : ∃ G : R3 → ℝ, Continuous G ∧
      ∀ᵐ x ∂(volume : Measure R3).restrict ballOpens, x ∈ closedBall (0 : R3) a →
        G x = TauCeti.Wkp.value 2 (unitBallCoordinateDerivativeL hcalc 2 i U) x :=
    exists_continuous_representative_on_innerBall_of_nativeH2 hcalc
      (unitBallCoordinateDerivativeL hcalc 2 i U) a ha ha1
  choose G hG hGrep using hExist
  let u : BallH1 := TauCeti.Wkp.firstOrder 2 U
  have hGi (i : Fin 3) : ∀ᵐ x ∂(volume : Measure R3).restrict (ball (0 : R3) a),
      G i x = (TauCeti.W1p.gradient u x) i := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAB (hGrep i),
      ae_restrict_of_ae_restrict_of_subset hAB (unitBallCoordinateDerivativeL_value_ae hcalc 2 i U),
      ae_restrict_mem isOpen_ball.measurableSet] with x hx hd hxA
    exact (hx (ball_subset_closedBall hxA)).trans hd
  have hAll : ∀ᵐ x ∂(volume : Measure R3).restrict (ball (0 : R3) a),
      ∀ i : Fin 3, G i x = (TauCeti.W1p.gradient u x) i := ae_all_iff.mpr hGi
  let Q : R3 → R3 := fun x => ∑ i : Fin 3, G i x • coordinateVector i
  have hQ : Continuous Q := by
    exact continuous_finset_sum Finset.univ (fun i _ => (hG i).smul continuous_const)
  have hQA : (TauCeti.W1p.gradient u : R3 → R3)
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
  have hUA : (TauCeti.W1p.value u : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict Ω] F := by
    filter_upwards [hFA] with x hx
    exact (congrArg (fun f : BallSobolev 0 => (f : R3 → ℝ) x) (TauCeti.Wkp.value_firstOrder 2 U)).trans hx
  have hField : (fun x => innerSL ℝ (TauCeti.W1p.gradient u x))
      =ᵐ[(volume : Measure R3).restrict Ω] (fun x => innerSL ℝ (Q x)) := by
    filter_upwards [hQA] with x hx
    exact congrArg (innerSL ℝ) hx
  have hw := (((TauCeti.W1p.hasWeakFDerivOn u).mono hΩB).congr_ae hUA).congr_ae_deriv hField
  exact ⟨F, Q, hF, hQ, hFA, hQA, hw⟩

theorem exists_classical_nativeH3_valueGradient_on_innerBall
    (hcalc : FixedSobolevCalculus) (U : BallSobolev 3)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ (F : R3 → ℝ) (Q : R3 → R3), Continuous F ∧ Continuous Q ∧
      ((TauCeti.Wkp.value 3 U : R3 → ℝ) =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F) ∧
      ((TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 2 U) : R3 → R3)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] Q) ∧
      ∀ x ∈ ball (0 : R3) a, HasFDerivAt F (innerSL ℝ (Q x)) x := by
  obtain ⟨F, Q, hF, hQ, hValue, hGrad, hWeak⟩ :=
    exists_continuous_nativeH3_valueGradient_on_innerBall hcalc U a ha ha1
  refine ⟨F, Q, hF, hQ, hValue, hGrad, ?_⟩
  intro x hx
  exact hasFDerivAt_of_continuous_weakFDerivOn ⟨ball (0 : R3) a, isOpen_ball⟩
    F (fun y => innerSL ℝ (Q y)) hF ((innerSL ℝ).continuous.comp hQ) hWeak x hx

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_continuous_nativeH3_valueGradient_on_innerBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_classical_nativeH3_valueGradient_on_innerBall
