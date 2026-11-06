import Calderon.PositiveCoefficientInnerSmoothRepresentative
import Calderon.NativeInteriorH3ClassicalJet

/-! Full upfront: EXPANSION.json. Actual native/classical first jet and compact-test weak PDE.
No representative/gradient/physical harmonicity premise is added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace Matrix
open scoped ENNReal ContDiff InnerProductSpace Topology Gradient Distributions Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge MetricVolume

theorem smoothSobolev_mem_zero_of_compact_support_inside
    (φ : SmoothData) (hCompact : HasCompactSupport φ.1)
    (hSupport : tsupport φ.1 ⊆ (ballOpens : Set R3)) :
    smoothSobolev φ ∈ TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2 := by
  let ψ : 𝓓(ballOpens, ℝ) := ⟨φ.1,φ.2,hCompact,hSupport⟩
  have hEq : smoothSobolev φ = testFunctionSobolev ψ := smoothSobolev_testFunction ψ
  rw [hEq]
  exact testFunctionSobolev_mem_w1p0 ψ

theorem exists_contDiffOn_positiveCoefficientDirichletSolution_valueGradient_innerBall
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ F : R3 → ℝ, Continuous F ∧ ContDiffOn ℝ ∞ F (ball (0 : R3) a) ∧
      ((TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F) ∧
      ((TauCeti.W1p.gradient (positiveCoefficientDirichletSolution A hA hPos f) : R3 → R3)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] gradient F) := by
  obtain ⟨F,hF,hSmooth,hFrep⟩ :=
    exists_contDiffOn_positiveCoefficientDirichletSolution_innerBall hcalc hreg τ0 A hA hPos f a ha ha1
  obtain ⟨U,hU,hLower⟩ :=
    exists_coherent_positiveCoefficientDirichletSolution_allOrderLifts hcalc hreg τ0 A hA hPos f
  obtain ⟨G,Q,hG,hQ,hGvalue,hGgradient,hGD⟩ :=
    exists_classical_nativeH3_valueGradient_on_innerBall hcalc (U 1) a ha ha1
  have hValueEq : TauCeti.Wkp.value 3 (U 1) =
      TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) := by
    simpa only [TauCeti.Wkp.value_firstOrder] using
      congrArg (fun u : BallH1 => TauCeti.W1p.value u) (hU 1)
  have hGrep : (TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) : R3 → ℝ)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] G := by
    filter_upwards [hGvalue] with x hx
    exact (congrArg (fun p : BallSobolev 0 => (p : R3 → ℝ) x) hValueEq).symm.trans hx
  have hGradientEq : TauCeti.W1p.gradient (TauCeti.Wkp.firstOrder 2 (U 1)) =
      TauCeti.W1p.gradient (positiveCoefficientDirichletSolution A hA hPos f) :=
    congrArg TauCeti.W1p.gradient (hU 1)
  have hNativeGradient : (TauCeti.W1p.gradient (positiveCoefficientDirichletSolution A hA hPos f) : R3 → R3)
      =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] Q := by
    filter_upwards [hGgradient] with x hx
    exact (congrArg (fun p : Lp R3 2 ((volume : Measure R3).restrict ballOpens) =>
      (p : R3 → R3) x) hGradientEq).symm.trans hx
  have hEq : EqOn F G (ball (0 : R3) a) :=
    Measure.eqOn_open_of_ae_eq (hFrep.symm.trans hGrep) isOpen_ball hF.continuousOn hG.continuousOn
  have hClassicalGradient (x : R3) (hx : x ∈ ball (0 : R3) a) : gradient F x = Q x := by
    have hNear : F =ᶠ[𝓝 x] G := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hEq hy
    have hDual : InnerProductSpace.toDual ℝ R3 (Q x) = innerSL ℝ (Q x) := rfl
    have hGradient : HasGradientAt G (Q x) x := by
      rw [hasGradientAt_iff_hasFDerivAt,hDual]
      exact hGD x hx
    exact hNear.gradient_eq.trans hGradient.gradient
  refine ⟨F,hF,hSmooth,hFrep,?_⟩
  filter_upwards [hNativeGradient,ae_restrict_mem isOpen_ball.measurableSet] with x hx hxA
  exact hx.trans (hClassicalGradient x hxA).symm

theorem exists_positiveCoefficientDirichletSolution_classical_weakEquation_innerBall
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (τ0 : UnitBallValueTrace)
    (A : MatrixField) (hA : ContDiff ℝ ∞ A) (hPos : ∀ x, (A x).PosDef) (f : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ F : R3 → ℝ, Continuous F ∧ ContDiffOn ℝ ∞ F (ball (0 : R3) a) ∧
      ((TauCeti.W1p.value (positiveCoefficientDirichletSolution A hA hPos f) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) a)] F) ∧
      ∀ φ : SmoothData, HasCompactSupport φ.1 → tsupport φ.1 ⊆ ball (0 : R3) a →
        ∫ x : R3, (gradient φ.1 x : R3) ⬝ᵥ (A x *ᵥ (gradient F x : R3)) ∂(volume : Measure R3) = 0 := by
  obtain ⟨F,hF,hSmooth,hValue,hGradient⟩ :=
    exists_contDiffOn_positiveCoefficientDirichletSolution_valueGradient_innerBall
      hcalc hreg τ0 A hA hPos f a ha ha1
  refine ⟨F,hF,hSmooth,hValue,?_⟩
  intro φ hCompact hSupport
  have hAB : ball (0 : R3) a ⊆ (ballOpens : Set R3) := by
    intro x hx
    change dist x (0 : R3) < 1
    exact (show dist x (0 : R3) < a from hx).trans ha1
  have hMem := smoothSobolev_mem_zero_of_compact_support_inside φ hCompact (hSupport.trans hAB)
  let v : BallH1Zero := ⟨smoothSobolev φ,hMem⟩
  have hWeak : TauCeti.PDE.energyFormH1 A 0 0
      (positiveCoefficientDirichletSolution A hA hPos f) (smoothSobolev φ) = 0 :=
    positiveCoefficientDirichletSolution_weakEquation A hA hPos f v
  have hGradGlobal : ∀ᵐ x ∂(volume : Measure R3), x ∈ ball (0 : R3) a →
      TauCeti.W1p.gradient (positiveCoefficientDirichletSolution A hA hPos f) x = gradient F x :=
    (ae_restrict_iff' isOpen_ball.measurableSet).mp hGradient
  have hZeroOutside (x : R3) (hx : x ∉ ball (0 : R3) a) : gradient φ.1 x = 0 := by
    have hNot : x ∉ tsupport φ.1 := fun hs => hx (hSupport hs)
    have hD : fderiv ℝ φ.1 x = 0 := fderiv_of_notMem_tsupport ℝ hNot
    simp only [gradient,hD,map_zero]
  let d : R3 → ℝ := fun x => (gradient φ.1 x : R3) ⬝ᵥ (A x *ᵥ (gradient F x : R3))
  have hEnergy : TauCeti.PDE.energyFormH1 A 0 0
      (positiveCoefficientDirichletSolution A hA hPos f) (smoothSobolev φ) =
      ∫ x in ballOpens, d x ∂(volume : Measure R3) := by
    rw [TauCeti.PDE.energyFormH1_def]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hGradGlobal,gradient_smoothSobolev_ae φ] with x hx hTest
    simp only [TauCeti.PDE.energyIntegrand_apply,TauCeti.PDE.jetField_apply,
      TauCeti.PDE.matrixBilinearForm_apply,TauCeti.PDE.driftForm_apply,TauCeti.PDE.massForm_apply,
      Pi.zero_apply,inner_zero_left,zero_mul,add_zero]
    rw [hTest]
    by_cases hxA : x ∈ ball (0 : R3) a
    · rw [hx hxA]
    · dsimp only [d]
      rw [hZeroOutside x hxA]
      simp
  have hIntegral : ∫ x in ballOpens, d x ∂(volume : Measure R3) = 0 := hEnergy.symm.trans hWeak
  have hSupportB (x : R3) (hx : x ∉ (ballOpens : Set R3)) : d x = 0 := by
    have hxA : x ∉ ball (0 : R3) a := fun hy => hx (hAB hy)
    dsimp only [d]
    rw [hZeroOutside x hxA]
    simp
  have hGlobal : (∫ x in ballOpens, d x ∂(volume : Measure R3)) =
      ∫ x, d x ∂(volume : Measure R3) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hSupportB
  exact hGlobal.symm.trans hIntegral

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.smoothSobolev_mem_zero_of_compact_support_inside
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_contDiffOn_positiveCoefficientDirichletSolution_valueGradient_innerBall
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_positiveCoefficientDirichletSolution_classical_weakEquation_innerBall
