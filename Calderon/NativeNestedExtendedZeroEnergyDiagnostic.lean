import Calderon.NativeNestedMetricEnergyLocalization
import Calderon.NativeRestrictedZeroTestEnergy

/-! EXPANSION.json precedes this exact focused source restriction diagnostic. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

#eval (show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "ZERO ENERGY DECL BEGIN"
  out.flush)

lemma energyFormH1_extendedZeroTest_eq_restriction (Omega OmegaOuter : Opens R3)
    (hsub : Omega ≤ OmegaOuter) (A : MatrixField)
    (hc : MemLp (fun x => TauCeti.PDE.energyIntegrand (A x) 0 0) ⊤
      ((volume : Measure R3).restrict OmegaOuter))
    (U : TauCeti.W1p (volume : Measure R3) OmegaOuter 2)
    (z : TauCeti.W1p0 (volume : Measure R3) Omega 2) :
    TauCeti.PDE.energyFormH1 A 0 0 U
      (TauCeti.W1p0.extendByZeroL hsub z : TauCeti.W1p (volume : Measure R3) OmegaOuter 2) =
    TauCeti.PDE.energyFormH1 A 0 0 (TauCeti.W1p.restrictL hsub U)
      (z : TauCeti.W1p (volume : Measure R3) Omega 2) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ZERO ENERGY PROOF ENTER"
    out.flush
  let V : TauCeti.W1p (volume : Measure R3) OmegaOuter 2 := TauCeti.W1p0.extendByZeroL hsub z
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ZERO TEST MADE"
    out.flush
  let D : R3 → ℝ := fun x => TauCeti.PDE.energyIntegrand (A x) 0 0
    (TauCeti.PDE.jetField U x) (TauCeti.PDE.jetField V x)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "DENSITY MADE"
    out.flush
  have hValue : TauCeti.W1p.value V =ᵐ[(volume : Measure R3).restrict OmegaOuter]
      (Omega : Set R3).indicator
        (TauCeti.W1p.value (z : TauCeti.W1p (volume : Measure R3) Omega 2) : R3 → ℝ) := by
    dsimp only [V]
    rw [TauCeti.W1p0.value_extendByZeroL]
    exact TauCeti.coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr hsub) _
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "VALUE INDICATOR COMPLETE"
    out.flush
  have hGradient : TauCeti.W1p.gradient V =ᵐ[(volume : Measure R3).restrict OmegaOuter]
      (Omega : Set R3).indicator
        (TauCeti.W1p.gradient (z : TauCeti.W1p (volume : Measure R3) Omega 2) : R3 → R3) := by
    dsimp only [V]
    rw [TauCeti.W1p0.gradient_extendByZeroL]
    exact TauCeti.coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr hsub) _
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "GRADIENT INDICATOR COMPLETE"
    out.flush
  have hOutside : ∀ᵐ x ∂(volume : Measure R3).restrict OmegaOuter,
      x ∉ (Omega : Set R3) → D x = 0 := by
    filter_upwards [hValue,hGradient] with x hv hd hx
    dsimp only [D]
    rw [TauCeti.PDE.jetField_apply,TauCeti.PDE.jetField_apply,hv,hd,
      Set.indicator_of_notMem hx,Set.indicator_of_notMem hx]
    exact map_zero (TauCeti.PDE.energyIntegrand (A x) 0 0
      (TauCeti.W1p.value U x,TauCeti.W1p.gradient U x))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ZERO OUTSIDE COMPLETE"
    out.flush
  have hInt : IntegrableOn D OmegaOuter (volume : Measure R3) :=
    TauCeti.PDE.integrable_energyIntegrand_jetField hc U V
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "DENSITY INTEGRABLE COMPLETE"
    out.flush
  have hLoc := setIntegral_difference_eq_inner Omega OmegaOuter hsub D (fun _ => 0)
    hInt (MeasureTheory.integrable_zero R3 ℝ ((volume : Measure R3).restrict OmegaOuter)) hOutside
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "SCALAR LOCALIZATION COMPLETE"
    out.flush
  have hIntegral : (∫ x in OmegaOuter, D x ∂(volume : Measure R3)) =
      ∫ x in Omega, D x ∂(volume : Measure R3) := by
    simpa only [integral_zero,sub_zero] using hLoc
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "INTEGRAL NORMALIZED COMPLETE"
    out.flush
  have hInner := energyFormH1_restrictedZeroTest_eq_setIntegral Omega OmegaOuter hsub A U z
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "INNER ENERGY COMPLETE"
    out.flush
  exact (TauCeti.PDE.energyFormH1_def A 0 0 U V).trans (hIntegral.trans hInner.symm)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "ZERO ENERGY BODY COMPLETE"
    out.flush

#eval (show IO Unit from do
  let out ← IO.getStdout
  out.putStrLn "ZERO ENERGY DECL END"
  out.flush)

end OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain
#print axioms OAI.AnisotropicCalderon.EnergyBridge.NativeNestedDomain.energyFormH1_extendedZeroTest_eq_restriction
