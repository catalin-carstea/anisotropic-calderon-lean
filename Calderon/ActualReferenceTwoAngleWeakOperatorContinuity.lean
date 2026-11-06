import Calderon.RealNormedCarrierContinuityTransport
import Mathlib.Topology.Instances.RealVectorSpace
import Calderon.ActualReferenceTwoAngleFullWeakEnergyTopology
import Calderon.ActualReferenceRotationWeakEnergy
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.ClmNaturalStructureData
import Calderon.SubmoduleRealNaturalStructureData
import Calderon.NativeWeakOperatorNormedStructures
import Calderon.NativeTwoAngleDualTestPostcompositionTopology


set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace


attribute [local instance]
  weakHeaderDualH1Group
  weakHeaderDualH1Space
  weakHeaderDualZeroGroup
  weakHeaderDualZeroSpace
  weakHeaderH1DualZeroGroup
  weakHeaderH1DualZeroSpace
  weakHeaderSelfDualGroup
  weakHeaderSelfDualSpace
  weakHeaderDualZeroH1ZeroGroup
  weakHeaderDualZeroH1ZeroSpace

attribute [local irreducible] referenceTwoAngleFullWeakEnergyFamily
  referenceTwoAngleWeakEnergyFamily referenceTwoAngleWeakDirichletEnergyFamily

lemma contDiff_referenceTwoAngleWeakEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleWeakEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l) := by
  unfold referenceTwoAngleWeakEnergyFamily
  exact contDiff_nativeTwoAngle_dual_test_postcomposition
    nativeH1ZeroDualRestrictionL
    (referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)
    (contDiff_referenceTwoAngleFullWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l)

@[defeq]
lemma submodule_normedAddCommGroup_addCommGroup_eq_natural
    {R V : Type*} [Ring R] [NormedAddCommGroup V] [Module R V]
    (s : Submodule R V) :
    (Submodule.normedAddCommGroup s).toAddCommGroup =
      Submodule.addCommGroup s := by
  rfl

@[defeq]
lemma lp_normedAddCommGroup_addCommGroup_eq_natural
    (A E : Type*) [MeasurableSpace A] [NormedAddCommGroup E]
    (p : ENNReal) [Fact (1 ≤ p)] (mu : Measure A) :
    (MeasureTheory.Lp.instNormedAddCommGroup (E := E) (p := p) (μ := mu)).toAddCommGroup =
      MeasureTheory.Lp.instAddCommGroup (E := E) (p := p) (μ := mu) := by
  rfl

lemma contDiff_referenceTwoAngleWeakDirichletEnergyFamily (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) :
    ContDiff ℝ ∞ (referenceTwoAngleWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l) := by
  let A : (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceTwoAngleWeakDirichletEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  let R : (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → BallH1 →L[ℝ] StrongDual ℝ BallH1Zero :=
    referenceTwoAngleWeakEnergyFamily g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  let J : BallH1Zero →L[ℝ] BallH1 :=
    (TauCeti.w1p0Submodule (volume : Measure R3) ballOpens 2).toSubmodule.subtypeL
  have hR := contDiff_referenceTwoAngleWeakEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  have hSmooth := contDiff_nativeWeakEnergy_precomposition R hR J
  have hLiteral : A = (fun t => (R t).comp J) := by
    funext t
    unfold A referenceTwoAngleWeakDirichletEnergyFamily
    rfl
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
      let ctx ← Lean.getLCtx
      let some hd := ctx.findFromUserName? `hSmooth
        | throwError "hSmooth missing"
      let source := (← Lean.instantiateMVars hd.type).consumeMData
      let sa := source.getAppArgs
      let ta := target.getAppArgs
      unless sa.size == 10 && ta.size == 10 do
        throwError "Expected exact ten-argument ContDiff applications"
      let he ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[5]! ta[5]!)
      let hg ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
      let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
      let ci ← Lean.getConstInfo ``contDiff_real_carrier_transport
      let c := Lean.mkConst ``contDiff_real_carrier_transport
        (ci.levelParams.map (fun _ => Lean.Level.zero))
      let proof := Lean.mkAppN c #[ta[2]!, sa[5]!, ta[5]!, ta[3]!, ta[4]!,
        sa[6]!, ta[6]!, sa[7]!, ta[7]!, he, hg, sa[9]!, ta[9]!, hf,
        Lean.mkFVar hd.fvarId]
      goal.assign proof
      Lean.Elab.Tactic.replaceMainGoal [he.mvarId!, hg.mvarId!, hf.mvarId!]
  · trace "CARRIER_EQUALITY"
    rfl
  · trace "GROUP_HEQUALITY"
    rfl
  · trace "FUNCTION_HEQUALITY"
    exact heq_of_eq hLiteral.symm



end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
