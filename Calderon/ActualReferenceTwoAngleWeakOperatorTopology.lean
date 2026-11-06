import Calderon.ActualReferenceTwoAngleWeakOperatorInverseOpen
import Calderon.ActualReferenceTwoAngleWeakOperatorContinuity
import Calderon.NativeWeakOperatorNormedStructures
import Calderon.ActualReferenceRotationWeakEnergy
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

import Calderon.ActualReferenceTwoAngleFullWeakEnergyTopology
import Calderon.ActualReferenceRotationWeakEnergy
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.ClmNaturalStructureData
import Calderon.SubmoduleRealNaturalStructureData
import Calderon.NativeWeakOperatorNormedStructures
import Calderon.NativeTwoAngleDualTestPostcompositionTopology

/-! Full upfront: high-degree-rotation-author-oct15-v001/
REPAIR-two-angle-weak-literal-covariance-topology-partition-v065.md. Exact selected-claim partition. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
private lemma real_clm_carrier_eq_of_data
    {E E' F F' : Type}
    (tE : TopologicalSpace E) (tE' : TopologicalSpace E')
    (aE : AddCommMonoid E) (aE' : AddCommMonoid E')
    (tF : TopologicalSpace F) (tF' : TopologicalSpace F')
    (aF : AddCommMonoid F) (aF' : AddCommMonoid F')
    (mE : @Module ℝ E Real.semiring aE)
    (mE' : @Module ℝ E' Real.semiring aE')
    (mF : @Module ℝ F Real.semiring aF)
    (mF' : @Module ℝ F' Real.semiring aF')
    (eE : E = E') (eF : F = F')
    (htE : HEq tE tE') (haE : HEq aE aE')
    (htF : HEq tF tF') (haF : HEq aF aF')
    (hmE : HEq mE mE') (hmF : HEq mF mF') :
    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E tE aE F tF aF mE mF =
    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E' tE' aE' F' tF' aF' mE' mF' := by
  subst E'
  subst F'
  cases eq_of_heq htE
  cases eq_of_heq haE
  cases eq_of_heq htF
  cases eq_of_heq haF
  cases eq_of_heq hmE
  cases eq_of_heq hmF
  rfl

private lemma real_clm_normedAddCommGroup_addCommMonoid_eq_natural
    (U K : Type) [NormedAddCommGroup U] [NormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toNormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toAddCommGroup.toAddCommMonoid =
    ContinuousLinearMap.addCommMonoid
      (M₁ := U) (M₂ := K) (σ₁₂ := RingHom.id ℝ) := by
  have hSemi := clm_normedAddCommGroup_seminormedAddCommGroup_eq U K
  have hAdd := congrArg
    (fun n : SeminormedAddCommGroup (U →L[ℝ] K) =>
      n.toAddCommGroup.toAddCommMonoid) hSemi
  exact hAdd.trans (clm_seminormedAddCommGroup_addCommMonoid_eq_natural U K)

private lemma real_clm_normedSpace_module_heq_natural
    (U K : Type) [SeminormedAddCommGroup U] [SeminormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    HEq (ContinuousLinearMap.module (S₃ := ℝ) (M := U) (M₃ := K) (σ₁₃ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toModule := by
  exact heq_of_eq (clm_normedSpace_module_eq_natural U K).symm

private lemma real_clm_normedAddCommGroup_topology_eq_natural
    (U K : Type) [NormedAddCommGroup U] [NormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toNormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    ContinuousLinearMap.topologicalSpace
      (E := U) (F := K) (σ := RingHom.id ℝ) := by
  have hSemi := clm_normedAddCommGroup_seminormedAddCommGroup_eq U K
  have hTop := congrArg
    (fun n : SeminormedAddCommGroup (U →L[ℝ] K) =>
      n.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) hSemi
  exact hTop.trans (clm_seminormedAddCommGroup_topologicalSpace_eq_natural U K)

private lemma real_clm_isInvertible_carrier_eq
    {E E' F F' : Type}
    (tE : TopologicalSpace E) (tE' : TopologicalSpace E')
    (aE : AddCommMonoid E) (aE' : AddCommMonoid E')
    (tF : TopologicalSpace F) (tF' : TopologicalSpace F')
    (aF : AddCommMonoid F) (aF' : AddCommMonoid F')
    (mE : @Module ℝ E Real.semiring aE)
    (mE' : @Module ℝ E' Real.semiring aE')
    (mF : @Module ℝ F Real.semiring aF)
    (mF' : @Module ℝ F' Real.semiring aF')
    (eE : E = E') (eF : F = F')
    (htE : HEq tE tE') (haE : HEq aE aE')
    (htF : HEq tF tF') (haF : HEq aF aF')
    (hmE : HEq mE mE') (hmF : HEq mF mF')
    (f : @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E tE aE F tF aF mE mF)
    (g : @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E' tE' aE' F' tF' aF' mE' mF') (hf : HEq f g) :
    @ContinuousLinearMap.IsInvertible ℝ E F tE tF Real.semiring aE mE aF mF f =
    @ContinuousLinearMap.IsInvertible ℝ E' F' tE' tF' Real.semiring aE' mE' aF' mF' g := by
  subst E'
  subst F'
  cases eq_of_heq htE
  cases eq_of_heq haE
  cases eq_of_heq htF
  cases eq_of_heq haF
  cases eq_of_heq hmE
  cases eq_of_heq hmF
  cases eq_of_heq hf
  rfl

private lemma real_clm_inverse_function_carrier_heq
    {P E E' F F' : Type}
    (tE : TopologicalSpace E) (tE' : TopologicalSpace E')
    (aE : AddCommMonoid E) (aE' : AddCommMonoid E')
    (tF : TopologicalSpace F) (tF' : TopologicalSpace F')
    (aF : AddCommMonoid F) (aF' : AddCommMonoid F')
    (mE : @Module ℝ E Real.semiring aE)
    (mE' : @Module ℝ E' Real.semiring aE')
    (mF : @Module ℝ F Real.semiring aF)
    (mF' : @Module ℝ F' Real.semiring aF')
    (eE : E = E') (eF : F = F')
    (htE : HEq tE tE') (haE : HEq aE aE')
    (htF : HEq tF tF') (haF : HEq aF aF')
    (hmE : HEq mE mE') (hmF : HEq mF mF')
    (f : P → @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E tE aE F tF aF mE mF)
    (g : P → @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E' tE' aE' F' tF' aF' mE' mF') (hf : HEq f g) :
    HEq (fun z => @ContinuousLinearMap.inverse ℝ E F tE tF Real.semiring aE mE aF mF (f z))
      (fun z => @ContinuousLinearMap.inverse ℝ E' F' tE' tF' Real.semiring aE' mE' aF' mF' (g z)) := by
  subst E'
  subst F'
  cases eq_of_heq htE
  cases eq_of_heq haE
  cases eq_of_heq htF
  cases eq_of_heq haF
  cases eq_of_heq hmE
  cases eq_of_heq hmF
  cases eq_of_heq hf
  rfl

-- Constructor congruence. Its proof only substitutes exact data and uses
-- proof irrelevance for RingHomIsometric; the operator norm is never unfolded.
private lemma clm_normedAddCommGroup_constructor_heq
    {K L E E' F F' : Type}
    [rK : NontriviallyNormedField K] [rL : NontriviallyNormedField L]
    (gE : NormedAddCommGroup E) (gE' : NormedAddCommGroup E')
    (gF : NormedAddCommGroup F) (gF' : NormedAddCommGroup F')
    (sE : @NormedSpace K E rK.toNormedField gE.toSeminormedAddCommGroup)
    (sE' : @NormedSpace K E' rK.toNormedField gE'.toSeminormedAddCommGroup)
    (sF : @NormedSpace L F rL.toNormedField gF.toSeminormedAddCommGroup)
    (sF' : @NormedSpace L F' rL.toNormedField gF'.toSeminormedAddCommGroup)
    (σ : K →+* L) (i j : RingHomIsometric σ)
    (eE : E = E') (eF : F = F')
    (hgE : HEq gE gE') (hgF : HEq gF gF')
    (hsE : HEq sE sE') (hsF : HEq sF sF') :
    HEq
      (letI := gE; letI := gF; letI := sE; letI := sF; letI := i
       ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := F) (σ₁₂ := σ))
      (letI := gE'; letI := gF'; letI := sE'; letI := sF'; letI := j
       ContinuousLinearMap.toNormedAddCommGroup (E := E') (F := F') (σ₁₂ := σ)) := by
  subst E'
  subst F'
  have he : gE = gE' := eq_of_heq hgE
  cases he
  have hf : gF = gF' := eq_of_heq hgF
  cases hf
  have hse : sE = sE' := eq_of_heq hsE
  cases hse
  have hsf : sF = sF' := eq_of_heq hsF
  cases hsf
  rfl

-- An optional subsidiary certificate for real-space arguments. Its premise
-- identifies the COMPLETE normed group, not only additive or topology data.
private lemma real_normedSpace_carrier_heq
    {E F : Type}
    (g : NormedAddCommGroup E) (h : NormedAddCommGroup F)
    (s : @NormedSpace ℝ E Real.normedField g.toSeminormedAddCommGroup)
    (t : @NormedSpace ℝ F Real.normedField h.toSeminormedAddCommGroup)
    (e : E = F) (hg : HEq g h) : HEq s t := by
  subst F
  have hgh : g = h := eq_of_heq hg
  cases hgh
  letI := g
  exact heq_of_eq (real_normedSpace_eq s t)

private lemma contDiffAt_real_carrier_transport
    {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : NormedAddCommGroup E) (h : NormedAddCommGroup F)
    (s : @NormedSpace ℝ E _ g.toSeminormedAddCommGroup)
    (t : @NormedSpace ℝ F _ h.toSeminormedAddCommGroup)
    (e : E = F) (hg : HEq g h) (f : P → E) (k : P → F)
    (hf : HEq f k) (x y : P) (hxy : x = y)
    (hc : letI := g; letI := s; ContDiffAt ℝ ∞ f x) :
    letI := h; letI := t; ContDiffAt ℝ ∞ k y := by
  subst F
  have hgh : g = h := eq_of_heq hg
  cases hgh
  letI := g
  cases real_normedSpace_eq s t
  have hfk : f = k := eq_of_heq hf
  cases hfk
  cases hxy
  exact hc

private lemma contDiffAt_clm_inverse_from_family
    {P U V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace U]
    (A : P → U →L[ℝ] V) (p : P) (hA : ContDiff ℝ ∞ A)
    (hInv : (A p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => (A z).inverse) p := by
  exact hInv.contDiffAt_map_inverse.comp p hA.contDiffAt


variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace



section CanonicalInverseInput
attribute [local instance] weakHeaderDualZeroGroup weakHeaderDualZeroSpace

private lemma contDiff_referenceTwoAngleWeakDirichletEnergyFamily_canonical_input
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    ContDiff (E := ℝ × (ℝ × (ℝ × (R3 × ℝ))))
      (F := BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) ℝ ∞
      (referenceTwoAngleWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l) := by
  have hA := contDiff_referenceTwoAngleWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let some hd := ctx.findFromUserName? `hA | throwError "hA missing"
      let source := (← Lean.instantiateMVars hd.type).consumeMData
      let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
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
      goal.assign (Lean.mkAppN c #[ta[2]!, sa[5]!, ta[5]!, ta[3]!, ta[4]!,
        sa[6]!, ta[6]!, sa[7]!, ta[7]!, he, hg, sa[9]!, ta[9]!, hf,
        Lean.mkFVar hd.fvarId])
      Lean.Elab.Tactic.replaceMainGoal [he.mvarId!, hg.mvarId!, hf.mvarId!]
  ·
    rfl
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let a := target.getAppArgs
        unless target.getAppFn.isConstOf ``HEq && a.size == 4 do
          throwError "Expected normed-group HEq"
        let mut lhs := a[1]!.consumeMData
        let mut rhs := a[3]!.consumeMData
        -- Unfold only a direct group alias, never a space or operator norm.
        for name in #[``weakHeaderSelfDualGroup, ``weakHeaderDualZeroH1ZeroGroup] do
          if lhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            lhs := body.consumeMData
          if rhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            rhs := body.consumeMData
        let la := lhs.getAppArgs
        let ra := rhs.getAppArgs
        unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            rhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            la.size == 12 && ra.size == 12 do
          throwError "Expected exact twelve-argument normed CLM constructors"
        for n in (#[0,1,6,7,10] : Array Nat) do
          unless la[n]! == ra[n]! do
            throwError "Fixed scalar constructor data changed at {n}"
        let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[2]! ra[2]!)
        let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[3]! ra[3]!)
        let hgE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[4]! ra[4]!)
        let hgF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[5]! ra[5]!)
        let hsE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[8]! ra[8]!)
        let hsF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[9]! ra[9]!)
        let ci ← Lean.getConstInfo ``clm_normedAddCommGroup_constructor_heq
        let c := Lean.mkConst ``clm_normedAddCommGroup_constructor_heq
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[la[0]!, la[1]!, la[2]!, ra[2]!, la[3]!, ra[3]!,
          la[6]!, la[7]!, la[4]!, ra[4]!, la[5]!, ra[5]!,
          la[8]!, ra[8]!, la[9]!, ra[9]!, la[10]!, la[11]!, ra[11]!,
          eE, eF, hgE, hgF, hsE, hsF])
        Lean.Elab.Tactic.replaceMainGoal
          [eE.mvarId!, eF.mvarId!, hgE.mvarId!, hgF.mvarId!, hsE.mvarId!, hsF.mvarId!]
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
  ·
    rfl

private lemma nativeTwoAngleInverseReverseGroupData :
    HEq
      (ContinuousLinearMap.toNormedAddCommGroup
        (E := StrongDual ℝ BallH1Zero) (F := BallH1Zero)
        (σ₁₂ := RingHom.id ℝ))
      weakHeaderDualZeroH1ZeroGroup := by
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
      let a := target.getAppArgs
      unless target.getAppFn.isConstOf ``HEq && a.size == 4 do
        throwError "Expected normed-group HEq"
      let mut lhs := a[1]!.consumeMData
      let mut rhs := a[3]!.consumeMData
      -- Unfold only a direct group alias, never a space or operator norm.
      for name in #[``weakHeaderSelfDualGroup, ``weakHeaderDualZeroH1ZeroGroup] do
        if lhs.getAppFn.isConstOf name then
          let ci ← Lean.getConstInfo name
          let some body := ci.value? | throwError "Simple group body unavailable"
          lhs := body.consumeMData
        if rhs.getAppFn.isConstOf name then
          let ci ← Lean.getConstInfo name
          let some body := ci.value? | throwError "Simple group body unavailable"
          rhs := body.consumeMData
      let la := lhs.getAppArgs
      let ra := rhs.getAppArgs
      unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
          rhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
          la.size == 12 && ra.size == 12 do
        throwError "Expected exact twelve-argument normed CLM constructors"
      for n in (#[0,1,6,7,10] : Array Nat) do
        unless la[n]! == ra[n]! do
          throwError "Fixed scalar constructor data changed at {n}"
      let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[2]! ra[2]!)
      let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[3]! ra[3]!)
      let hgE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[4]! ra[4]!)
      let hgF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[5]! ra[5]!)
      let hsE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[8]! ra[8]!)
      let hsF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[9]! ra[9]!)
      let ci ← Lean.getConstInfo ``clm_normedAddCommGroup_constructor_heq
      let c := Lean.mkConst ``clm_normedAddCommGroup_constructor_heq
        (ci.levelParams.map (fun _ => Lean.Level.zero))
      goal.assign (Lean.mkAppN c #[la[0]!, la[1]!, la[2]!, ra[2]!, la[3]!, ra[3]!,
        la[6]!, la[7]!, la[4]!, ra[4]!, la[5]!, ra[5]!,
        la[8]!, ra[8]!, la[9]!, ra[9]!, la[10]!, la[11]!, ra[11]!,
        eE, eF, hgE, hgF, hsE, hsF])
      Lean.Elab.Tactic.replaceMainGoal
        [eE.mvarId!, eF.mvarId!, hgE.mvarId!, hgF.mvarId!, hsE.mvarId!, hsF.mvarId!]
  ·
    rfl
  ·
    rfl
  ·
    rfl
  ·
    rfl
  ·
    rfl
  ·
    rfl

end CanonicalInverseInput

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


private def nativeTwoAngleInverseRegularityFact :=
  contDiffAt_clm_inverse_from_family
    (P := ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (U := BallH1Zero) (V := StrongDual ℝ BallH1Zero)

private def referenceTwoAngleWeakInverseCanonicalProof (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hInv : (referenceTwoAngleWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible) := by
  let A := referenceTwoAngleWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  let p := t
  have hA := contDiff_referenceTwoAngleWeakDirichletEnergyFamily_canonical_input
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l

  have hF := nativeTwoAngleInverseRegularityFact
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let some fd := ctx.findFromUserName? `hF | throwError "hF missing"
      let some ad := ctx.findFromUserName? `A | throwError "A missing"
      let some pd := ctx.findFromUserName? `p | throwError "p missing"
      let inverseApplication := Lean.mkAppN (Lean.mkFVar fd.fvarId)
        #[Lean.mkFVar ad.fvarId, Lean.mkFVar pd.fvarId]
      let ht ← Lean.Meta.whnf (← Lean.Meta.inferType inverseApplication)
      unless ht.isForall do throwError "Missing expected ContDiff binder"
      let ha ← Lean.Meta.mkFreshExprMVar ht.bindingDomain!
      let partial2 := Lean.mkApp inverseApplication ha
      let ht2 ← Lean.Meta.whnf (← Lean.Meta.inferType partial2)
      unless ht2.isForall do throwError "Missing expected IsInvertible binder"
      let hi ← Lean.Meta.mkFreshExprMVar ht2.bindingDomain!
      let result := Lean.mkApp partial2 hi
      let resultType ← Lean.Meta.inferType result
      unless ← Lean.Meta.isDefEq (← goal.getType) resultType do
        throwError "Inferred canonical result type mismatch"
      goal.assign result
      Lean.Elab.Tactic.replaceMainGoal [ha.mvarId!,hi.mvarId!]
  ·
    simpa only [A] using hA
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let ctx ← Lean.getLCtx
        let some hd := ctx.findFromUserName? `hInv | throwError "hInv missing"
        let source := hd.type
        let target ← goal.getType
        let he ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq source target)
        let ci ← Lean.getConstInfo ``Eq.mp
        let mp := Lean.mkConst ``Eq.mp (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN mp #[source, target, he, Lean.mkFVar hd.fvarId])
        Lean.Elab.Tactic.replaceMainGoal [he.mvarId!]
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let ea := target.getAppArgs
        let lhs := ea[1]!.consumeMData
        let rhs := ea[2]!.consumeMData
        let sa := lhs.getAppArgs
        let ta := rhs.getAppArgs
        unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.IsInvertible &&
            rhs.getAppFn.isConstOf ``ContinuousLinearMap.IsInvertible && sa.size == 11 && ta.size == 11 do
          throwError "Expected two exact inverse predicates"
        let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[1]! ta[1]!)
        let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[2]! ta[2]!)
        let htE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[3]! ta[3]!)
        let haE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
        let htF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[4]! ta[4]!)
        let haF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[8]! ta[8]!)
        let hmE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[7]! ta[7]!)
        let hmF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
        let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[10]! ta[10]!)
        let ci ← Lean.getConstInfo ``real_clm_isInvertible_carrier_eq
        let c := Lean.mkConst ``real_clm_isInvertible_carrier_eq
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[sa[1]!,ta[1]!,sa[2]!,ta[2]!,
          sa[3]!,ta[3]!,sa[6]!,ta[6]!,sa[4]!,ta[4]!,sa[8]!,ta[8]!,
          sa[7]!,ta[7]!,sa[9]!,ta[9]!,eE,eF,htE,haE,htF,haF,hmE,hmF,
          sa[10]!,ta[10]!,hf])
        Lean.Elab.Tactic.replaceMainGoal
          [eE.mvarId!,eF.mvarId!,htE.mvarId!,haE.mvarId!,htF.mvarId!,haF.mvarId!,hmE.mvarId!,hmF.mvarId!,hf.mvarId!]
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          -- This definition is a direct library instance application. Inspect
          -- its arguments, not its normed-group proof or the DualZeroSpace.
          let di ← Lean.getConstInfo ``weakHeaderDualZeroGroup
          let some body := di.value? | throwError "DualZero group body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
            throwError "DualZero group is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected exact source/codomain normed groups in DualZero body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_topology_eq_natural
          let c := Lean.mkConst ``real_clm_normedAddCommGroup_topology_eq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
          let proofType := (← Lean.Meta.inferType proof).consumeMData
          let ea := proofType.getAppArgs
          unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected exact additive projection certificate"
          let rev ← Lean.Meta.mkAppM ``Eq.symm #[proof]
          let hp ← Lean.Meta.mkAppM ``heq_of_eq #[rev]
          goal.assign hp
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          -- This definition is a direct library instance application. Inspect
          -- its arguments, not its normed-group proof or the SelfDualSpace.
          let di ← Lean.getConstInfo ``weakHeaderDualZeroGroup
          let some body := di.value? | throwError "DualZero group body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
            throwError "DualZero group is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected exact source/codomain normed groups in DualZero body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
          let c := Lean.mkConst ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
          let proofType := (← Lean.Meta.inferType proof).consumeMData
          let ea := proofType.getAppArgs
          unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected exact additive projection certificate"
          let si ← Lean.getConstInfo ``Eq.symm
          let symm := Lean.mkConst ``Eq.symm
            (si.levelParams.map (fun _ => Lean.Level.succ Lean.Level.zero))
          let rev := Lean.mkAppN symm #[ea[0]!, ea[1]!, ea[2]!, proof]
          let hp ← Lean.Meta.mkAppM ``heq_of_eq #[rev]
          goal.assign hp
    ·
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          let di ← Lean.getConstInfo ``weakHeaderDualZeroSpace
          let some body := di.value? | throwError "DualZero space body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedSpace do
            throwError "DualZero space is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``SeminormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected two exact seminormed groups in DualZero space body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedSpace_module_heq_natural
          let c := Lean.mkConst ``real_clm_normedSpace_module_heq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          goal.assign (Lean.mkAppN c #[u,k,groups[0]!.2,groups[1]!.2,su,sk])
    ·
      rfl

lemma contDiffAt_referenceTwoAngleWeak_inverse (hcalc : FixedSobolevCalculus)
    (i j k l : Fin 3) (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hInv : (referenceTwoAngleWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z => (referenceTwoAngleWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l z).inverse) t := by
  have hCanonical := referenceTwoAngleWeakInverseCanonicalProof
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l t hInv
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let some hd := ctx.findFromUserName? `hCanonical | throwError "Canonical conclusion missing"
      let result := Lean.mkFVar hd.fvarId
      let source := (← Lean.instantiateMVars (← Lean.Meta.inferType result)).consumeMData
      let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
      let sa := source.getAppArgs
      let ta := target.getAppArgs
      unless source.getAppFn.isConstOf ``ContDiffAt &&
          target.getAppFn.isConstOf ``ContDiffAt && sa.size == 11 && ta.size == 11 do
        throwError "Expected exact eleven-argument ContDiffAt applications"
      let he ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[5]! ta[5]!)
      let hg ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
      let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
      let hp ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[10]! ta[10]!)
      let ci ← Lean.getConstInfo ``contDiffAt_real_carrier_transport
      let c := Lean.mkConst ``contDiffAt_real_carrier_transport
        (ci.levelParams.map (fun _ => Lean.Level.zero))
      goal.assign (Lean.mkAppN c #[ta[2]!, sa[5]!, ta[5]!, ta[3]!, ta[4]!,
        sa[6]!, ta[6]!, sa[7]!, ta[7]!, he, hg, sa[9]!, ta[9]!, hf,
        sa[10]!, ta[10]!, hp, result])
      Lean.Elab.Tactic.replaceMainGoal
        [he.mvarId!, hg.mvarId!, hf.mvarId!, hp.mvarId!]
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let ea := target.getAppArgs
        let lhs := ea[1]!.consumeMData
        let rhs := ea[2]!.consumeMData
        let sa := lhs.getAppArgs
        let ta := rhs.getAppArgs
        unless lhs.getAppFn.isConstOf ``ContinuousLinearMap &&
            rhs.getAppFn.isConstOf ``ContinuousLinearMap && sa.size == 13 && ta.size == 13 do
          throwError "Expected exact reverse CLM carriers"
        let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[5]! ta[5]!)
        let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[8]! ta[8]!)
        let htE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
        let haE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[7]! ta[7]!)
        let htF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
        let haF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[10]! ta[10]!)
        let hmE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[11]! ta[11]!)
        let hmF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[12]! ta[12]!)
        let ci ← Lean.getConstInfo ``real_clm_carrier_eq_of_data
        let c := Lean.mkConst ``real_clm_carrier_eq_of_data
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[sa[5]!,ta[5]!,sa[8]!,ta[8]!,
          sa[6]!,ta[6]!,sa[7]!,ta[7]!,sa[9]!,ta[9]!,sa[10]!,ta[10]!,
          sa[11]!,ta[11]!,sa[12]!,ta[12]!,eE,eF,htE,haE,htF,haF,hmE,hmF])
        Lean.Elab.Tactic.replaceMainGoal
          [eE.mvarId!,eF.mvarId!,htE.mvarId!,haE.mvarId!,htF.mvarId!,haF.mvarId!,hmE.mvarId!,hmF.mvarId!]
    ·
      rfl
    ·
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          -- This definition is a direct library instance application. Inspect
          -- its arguments, not its normed-group proof or the DualZeroSpace.
          let di ← Lean.getConstInfo ``weakHeaderDualZeroGroup
          let some body := di.value? | throwError "DualZero group body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
            throwError "DualZero group is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected exact source/codomain normed groups in DualZero body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_topology_eq_natural
          let c := Lean.mkConst ``real_clm_normedAddCommGroup_topology_eq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
          let proofType := (← Lean.Meta.inferType proof).consumeMData
          let ea := proofType.getAppArgs
          unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected exact additive projection certificate"
          let hp ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
          goal.assign hp
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          -- This definition is a direct library instance application. Inspect
          -- its arguments, not its normed-group proof or the SelfDualSpace.
          let di ← Lean.getConstInfo ``weakHeaderDualZeroGroup
          let some body := di.value? | throwError "DualZero group body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
            throwError "DualZero group is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected exact source/codomain normed groups in DualZero body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
          let c := Lean.mkConst ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
          let proofType := (← Lean.Meta.inferType proof).consumeMData
          let ea := proofType.getAppArgs
          unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected exact additive projection certificate"
          let hp ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
          goal.assign hp
    ·
      rfl
    ·
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          let di ← Lean.getConstInfo ``weakHeaderDualZeroSpace
          let some body := di.value? | throwError "DualZero space body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedSpace do
            throwError "DualZero space is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``SeminormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected two exact seminormed groups in DualZero space body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedSpace_module_heq_natural
          let c := Lean.mkConst ``real_clm_normedSpace_module_heq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u,k,groups[0]!.2,groups[1]!.2,su,sk]
          let rev ← Lean.Meta.mkAppM ``HEq.symm #[proof]
          goal.assign rev
    ·
      rfl
  ·
    exact nativeTwoAngleInverseReverseGroupData
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let ea := target.getAppArgs
        unless target.getAppFn.isConstOf ``HEq && ea.size == 4 do
          throwError "Expected exact inverse-family HEq"
        Lean.Meta.lambdaTelescope ea[1]! fun xs lhs => do
          unless xs.size == 1 do throwError "Expected one parameter"
          let rhs := (ea[3]!.beta xs).consumeMData
          let lhs := lhs.consumeMData
          let sa := lhs.getAppArgs
          let ta := rhs.getAppArgs
          unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.inverse &&
              rhs.getAppFn.isConstOf ``ContinuousLinearMap.inverse && sa.size == 11 && ta.size == 11 do
            throwError "Expected exact inverse applications without unfolding"
          let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[1]! ta[1]!)
          let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[2]! ta[2]!)
          let htE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[3]! ta[3]!)
          let haE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
          let htF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[4]! ta[4]!)
          let haF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[8]! ta[8]!)
          let hmE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[7]! ta[7]!)
          let hmF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
          let fl ← Lean.Meta.mkLambdaFVars xs sa[10]!
          let fr ← Lean.Meta.mkLambdaFVars xs ta[10]!
          let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq fl fr)
          let ci ← Lean.getConstInfo ``real_clm_inverse_function_carrier_heq
          let c := Lean.mkConst ``real_clm_inverse_function_carrier_heq
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let paramType ← Lean.Meta.inferType xs[0]!
          goal.assign (Lean.mkAppN c #[paramType,sa[1]!,ta[1]!,sa[2]!,ta[2]!,
            sa[3]!,ta[3]!,sa[6]!,ta[6]!,sa[4]!,ta[4]!,sa[8]!,ta[8]!,
            sa[7]!,ta[7]!,sa[9]!,ta[9]!,eE,eF,htE,haE,htF,haF,hmE,hmF,fl,fr,hf])
          Lean.Elab.Tactic.replaceMainGoal
            [eE.mvarId!,eF.mvarId!,htE.mvarId!,haE.mvarId!,htF.mvarId!,haF.mvarId!,hmE.mvarId!,hmF.mvarId!,hf.mvarId!]
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          -- This definition is a direct library instance application. Inspect
          -- its arguments, not its normed-group proof or the DualZeroSpace.
          let di ← Lean.getConstInfo ``weakHeaderDualZeroGroup
          let some body := di.value? | throwError "DualZero group body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
            throwError "DualZero group is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected exact source/codomain normed groups in DualZero body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_topology_eq_natural
          let c := Lean.mkConst ``real_clm_normedAddCommGroup_topology_eq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
          let proofType := (← Lean.Meta.inferType proof).consumeMData
          let ea := proofType.getAppArgs
          unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected exact additive projection certificate"
          let hp ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
          goal.assign hp
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          -- This definition is a direct library instance application. Inspect
          -- its arguments, not its normed-group proof or the SelfDualSpace.
          let di ← Lean.getConstInfo ``weakHeaderDualZeroGroup
          let some body := di.value? | throwError "DualZero group body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
            throwError "DualZero group is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected exact source/codomain normed groups in DualZero body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
          let c := Lean.mkConst ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
          let proofType := (← Lean.Meta.inferType proof).consumeMData
          let ea := proofType.getAppArgs
          unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected exact additive projection certificate"
          let hp ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
          goal.assign hp
    ·
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          let di ← Lean.getConstInfo ``weakHeaderDualZeroSpace
          let some body := di.value? | throwError "DualZero space body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedSpace do
            throwError "DualZero space is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``SeminormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected two exact seminormed groups in DualZero space body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedSpace_module_heq_natural
          let c := Lean.mkConst ``real_clm_normedSpace_module_heq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u,k,groups[0]!.2,groups[1]!.2,su,sk]
          let rev ← Lean.Meta.mkAppM ``HEq.symm #[proof]
          goal.assign rev
    ·
      rfl
  ·
    rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleWeak_inverse
